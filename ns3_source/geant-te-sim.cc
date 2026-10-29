/*
 * geant-te-sim.cc  --  GEANT traffic-engineering replay in ns-3
 *
 * Replaces the earlier geant-cnn-lstm-multiflow.cc experiment.  What changed and why:
 *
 *   1. Baseline routing is IGP shortest path using the real IGP metrics from
 *      geant_link_capacities.csv (the old code used hop count).
 *   2. Link delays are per-link propagation delays (geo model) instead of a flat 5 ms.
 *   3. The whole 23x23 traffic matrix is injected as background traffic (every OD pair
 *      with a non-trivial rate), so the links the forecast says are hot really are hot.
 *   4. Time-varying: a window of consecutive 15-minute matrices is replayed back to back
 *      (each one for --interval-sec seconds of simulated time at its true rate) and the
 *      routes are recomputed at every interval boundary.
 *   5. Four controllers are compared on identical offered traffic:
 *         static    IGP shortest path, never changes
 *         reactive  load-aware weights from the LAST OBSERVED matrix (4 steps stale)
 *         proactive load-aware weights from the FORECAST matrix for this interval
 *         oracle    load-aware weights from the TRUE matrix (upper bound)
 *      This is the same reactive/proactive definition as the Python study.
 *   6. Metrics are mean/p95/p99 packet delay, jitter, loss, per-interval peak link
 *      utilisation, queue drops, route changes and IGP stretch -- not a summed delay.
 *   7. Optional link failure (--fail=u-v --fail-at=s) really takes the interfaces down
 *      inside the traffic window; routes are recomputed after --fail-reroute-ms.
 *   8. Routes can be logged (--route-log) and pcap enabled (--pcap-node) for inspection.
 *
 * Limits (also in the README): traffic is constant-rate UDP per OD pair per interval
 * (no intra-interval burstiness, no TCP); IGP convergence after a failure is modelled as
 * a fixed delay; propagation delays come from city-level coordinates, not real fibre.
 *
 * Tested against ns-3.44.  Build: copy to scratch/ and run  ./ns3 run "geant-te-sim ..."
 */

#include "ns3/applications-module.h"
#include "ns3/core-module.h"
#include "ns3/flow-monitor-module.h"
#include "ns3/internet-module.h"
#include "ns3/ipv4-static-routing-helper.h"
#include "ns3/network-module.h"
#include "ns3/point-to-point-module.h"
#include "ns3/traffic-control-module.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace ns3;

NS_LOG_COMPONENT_DEFINE("GeantTeSim");

namespace
{
constexpr uint32_t kN = 23;
constexpr uint16_t kPort = 9000;
constexpr double kInf = std::numeric_limits<double>::infinity();

using Matrix = std::vector<std::vector<double>>;

struct Link
{
    uint32_t u = 0;
    uint32_t v = 0;
    double capKbps = 0;  // already multiplied by --cap-scale
    double igp = 1;
    double delayMs = 1;
    bool up = true;
    uint32_t ifU = 0;
    uint32_t ifV = 0;
    Ipv4Address addrU;
    Ipv4Address addrV;
};

// nh[dst][node] = index of the link `node` uses to reach `dst` (-1 = unreachable)
struct Plan
{
    std::vector<std::vector<int>> nh;
};

struct PathInfo
{
    std::vector<int> nodes;
    std::vector<int> links;
    double igp = 0;
};

struct Sim
{
    std::vector<Link> links;
    std::vector<std::vector<std::pair<int, int>>> adj;  // node -> (link, neighbour)
    std::vector<Ipv4Address> destAddr;
    NodeContainer nodes;

    std::string mode = "static";
    double t0 = 1.0;
    double T = 0.25;
    double beta = 100.0;
    double trigger = 0.55;
    double hyst = 0.05;
    Plan prevPlan;
    bool havePrevPlan = false;
    std::vector<double> estIgp;
    std::vector<double> estChosen;
    double minFlowKbps = 50.0;
    double demandScale = 1.0;
    uint32_t nInt = 8;
    int iters = 4;

    std::vector<Matrix> tr;  // true demand per interval
    std::vector<Matrix> fc;  // forecast per interval
    std::vector<Matrix> ob;  // last observed per interval

    std::vector<std::vector<std::vector<int>>> prevPath;  // [s][d] -> node list
    bool havePrev = false;
    std::vector<double> routeChanges;
    std::vector<double> stretchNum;
    std::vector<double> stretchDen;
    std::vector<double> offeredKbps;

    std::vector<std::array<std::vector<double>, 2>> linkBytes;  // [link][dir][interval]
    std::ofstream routeLog;
    int currentInterval = 0;
};

Sim g;

// ------------------------------------------------------------------ helpers
std::vector<std::vector<std::string>>
ReadCsv(const std::string& file)
{
    std::ifstream in(file);
    if (!in)
    {
        std::cerr << "Cannot open " << file << "\n";
        std::exit(1);
    }
    std::vector<std::vector<std::string>> rows;
    std::string line;
    std::getline(in, line);  // header
    while (std::getline(in, line))
    {
        if (line.empty())
        {
            continue;
        }
        std::stringstream ss(line);
        std::vector<std::string> f;
        std::string x;
        while (std::getline(ss, x, ','))
        {
            f.push_back(x);
        }
        rows.push_back(f);
    }
    return rows;
}

Matrix
ZeroMatrix()
{
    return Matrix(kN, std::vector<double>(kN, 0.0));
}

// ------------------------------------------------------------------ routing
Plan
ComputeTrees(const std::vector<double>& w)
{
    Plan p;
    p.nh.assign(kN, std::vector<int>(kN, -1));
    for (uint32_t d = 0; d < kN; ++d)
    {
        std::vector<double> dist(kN, kInf);
        dist[d] = 0.0;
        using E = std::pair<double, uint32_t>;
        std::priority_queue<E, std::vector<E>, std::greater<E>> pq;
        pq.push({0.0, d});
        while (!pq.empty())
        {
            auto [c, u] = pq.top();
            pq.pop();
            if (c > dist[u])
            {
                continue;
            }
            for (const auto& [li, nb] : g.adj[u])
            {
                if (!g.links[li].up)
                {
                    continue;
                }
                double nd = c + w[li];
                if (nd < dist[nb] - 1e-9)
                {
                    dist[nb] = nd;
                    p.nh[d][nb] = li;
                    pq.push({nd, static_cast<uint32_t>(nb)});
                }
            }
        }
    }
    return p;
}

PathInfo
GetPath(const Plan& p, uint32_t s, uint32_t d)
{
    PathInfo out;
    out.nodes.push_back(s);
    uint32_t n = s;
    for (uint32_t guard = 0; n != d && guard < kN; ++guard)
    {
        int li = p.nh[d][n];
        if (li < 0)
        {
            return PathInfo();
        }
        const Link& L = g.links[li];
        n = (L.u == n) ? L.v : L.u;
        out.nodes.push_back(n);
        out.links.push_back(li);
        out.igp += L.igp;
    }
    if (n != d)
    {
        return PathInfo();
    }
    return out;
}

std::vector<std::array<double, 2>>
LinkLoads(const Plan& p, const Matrix& D)
{
    std::vector<std::array<double, 2>> load(g.links.size(), {0.0, 0.0});
    for (uint32_t s = 0; s < kN; ++s)
    {
        for (uint32_t d = 0; d < kN; ++d)
        {
            if (s == d || D[s][d] <= 0)
            {
                continue;
            }
            uint32_t n = s;
            for (uint32_t guard = 0; n != d && guard < kN; ++guard)
            {
                int li = p.nh[d][n];
                if (li < 0)
                {
                    break;
                }
                const Link& L = g.links[li];
                load[li][(L.u == n) ? 0 : 1] += D[s][d];
                n = (L.u == n) ? L.v : L.u;
            }
        }
    }
    return load;
}

// Estimated peak per-direction utilisation of `p` if demand `D` were routed over it.
double
EstPeak(const Plan& p, const Matrix& D)
{
    auto load = LinkLoads(p, D);
    double m = 0;
    for (size_t i = 0; i < g.links.size(); ++i)
    {
        m = std::max(m, std::max(load[i][0], load[i][1]) / g.links[i].capKbps);
    }
    return m;
}

// "Overflow" objective (as in the Python study): sum over links and directions of the
// squared utilisation excess above the trigger.  Zero when nothing is above the trigger.
double
Overflow(const Plan& p, const Matrix& D)
{
    auto load = LinkLoads(p, D);
    double o = 0;
    for (size_t i = 0; i < g.links.size(); ++i)
    {
        for (int dir = 0; dir < 2; ++dir)
        {
            double ex = load[i][dir] / g.links[i].capKbps - g.trigger;
            if (ex > 0)
            {
                o += ex * ex;
            }
        }
    }
    return o;
}

// D == nullptr: plain IGP shortest paths (the "static" controller).
// Otherwise a load-aware controller that only believes its own estimate:
//   1. If the IGP plan has no overflow (everything <= trigger) keep IGP.
//   2. Else generate candidate plans from weights  igp x (1 + beta * util^2)  (util from
//      method-of-successive-averages) and keep the candidate with the smallest ESTIMATED
//      overflow, but only if it beats the IGP plan.
//   3. Hysteresis: keep last interval's plan unless the new one cuts the estimated overflow
//      by more than a factor `hyst`, so routes do not flap on noise.
// `D` is the controller's view of demand: last-observed, forecast or true matrix.
Plan
BuildPlan(const Matrix* D, double* estIgp = nullptr, double* estChosen = nullptr, bool force = false)
{
    std::vector<double> w(g.links.size());
    for (size_t i = 0; i < g.links.size(); ++i)
    {
        w[i] = g.links[i].igp;
    }
    Plan base = ComputeTrees(w);
    if (!D)
    {
        return base;
    }
    double o0 = Overflow(base, *D);
    if (estIgp)
    {
        *estIgp = EstPeak(base, *D);
    }
    Plan best = base;
    double bo = o0;
    if (o0 > 0)
    {
        Plan plan = base;
        std::vector<std::array<double, 2>> avg(g.links.size(), {0.0, 0.0});
        for (int k = 0; k < g.iters; ++k)
        {
            auto load = LinkLoads(plan, *D);
            for (size_t i = 0; i < g.links.size(); ++i)
            {
                for (int dir = 0; dir < 2; ++dir)
                {
                    avg[i][dir] = (k == 0) ? load[i][dir]
                                           : avg[i][dir] * (k / (k + 1.0)) + load[i][dir] / (k + 1.0);
                }
                double u = std::max(avg[i][0], avg[i][1]) / g.links[i].capKbps;
                w[i] = g.links[i].igp * (1.0 + g.beta * u * u);
            }
            plan = ComputeTrees(w);
            double o = Overflow(plan, *D);
            if (o < bo - 1e-12)
            {
                best = plan;
                bo = o;
            }
        }
    }
    if (bo > 0 && g.havePrevPlan && !force)
    {
        double op = Overflow(g.prevPlan, *D);
        if (op <= bo * (1.0 + g.hyst) + 1e-12)
        {
            best = g.prevPlan;
            bo = op;
        }
    }
    if (estChosen)
    {
        *estChosen = EstPeak(best, *D);
    }
    return best;
}

void
InstallPlan(const Plan& plan)
{
    Ipv4StaticRoutingHelper helper;
    for (uint32_t n = 0; n < kN; ++n)
    {
        Ptr<Ipv4> ip = g.nodes.Get(n)->GetObject<Ipv4>();
        Ptr<Ipv4StaticRouting> sr = helper.GetStaticRouting(ip);
        for (uint32_t r = sr->GetNRoutes(); r-- > 0;)
        {
            if (sr->GetRoute(r).IsHost())
            {
                sr->RemoveRoute(r);  // only the /32 routes this program installed
            }
        }
        for (uint32_t d = 0; d < kN; ++d)
        {
            if (d == n)
            {
                continue;
            }
            int li = plan.nh[d][n];
            if (li < 0)
            {
                continue;
            }
            const Link& L = g.links[li];
            bool isU = (L.u == n);
            sr->AddHostRouteTo(g.destAddr[d], isU ? L.addrV : L.addrU, isU ? L.ifU : L.ifV);
        }
    }
}

const Matrix*
ControlMatrix(uint32_t i)
{
    if (g.mode == "reactive")
    {
        return &g.ob[i];
    }
    if (g.mode == "proactive")
    {
        return &g.fc[i];
    }
    if (g.mode == "oracle")
    {
        return &g.tr[i];
    }
    return nullptr;  // static
}

void
ApplyPlan(uint32_t i, bool boundary)
{
    g.currentInterval = static_cast<int>(i);
    double eI = 0;
    double eC = 0;
    Plan plan = BuildPlan(ControlMatrix(i), &eI, &eC, !boundary);
    Plan igpPlan = (g.mode == "static") ? plan : BuildPlan(nullptr);
    g.prevPlan = plan;
    g.havePrevPlan = true;
    InstallPlan(plan);
    if (boundary)
    {
        g.estIgp[i] = eI;
        g.estChosen[i] = eC;
    }

    double changes = 0;
    double num = 0;
    double den = 0;
    std::vector<std::vector<std::vector<int>>> cur(
        kN,
        std::vector<std::vector<int>>(kN));
    for (uint32_t s = 0; s < kN; ++s)
    {
        for (uint32_t d = 0; d < kN; ++d)
        {
            if (s == d)
            {
                continue;
            }
            PathInfo pi = GetPath(plan, s, d);
            cur[s][d] = pi.nodes;
            double dem = g.tr[i][s][d];
            if (dem < g.minFlowKbps || pi.nodes.empty())
            {
                continue;
            }
            PathInfo ref = GetPath(igpPlan, s, d);
            if (!ref.nodes.empty() && ref.igp > 0)
            {
                num += dem * pi.igp;
                den += dem * ref.igp;
            }
            if (g.havePrev && g.prevPath[s][d] != pi.nodes)
            {
                changes += 1;
            }
            if (g.routeLog.is_open())
            {
                g.routeLog << i << (boundary ? "" : "f") << "," << s << "," << d << ",";
                for (size_t k = 0; k < pi.nodes.size(); ++k)
                {
                    g.routeLog << (k ? "-" : "") << pi.nodes[k];
                }
                g.routeLog << "\n";
            }
        }
    }
    if (boundary)
    {
        g.routeChanges[i] = changes;
        g.stretchNum[i] = num;
        g.stretchDen[i] = den;
    }
    g.prevPath = cur;
    g.havePrev = true;
}

// ------------------------------------------------------------------ traffic source
// Constant-rate UDP source whose rate follows a per-interval schedule.
class TmSource : public Application
{
  public:
    void Configure(Ipv4Address src,
                   Ipv4Address dst,
                   uint32_t ipPktBytes,
                   std::vector<double> rateKbps,
                   double t0,
                   double T,
                   double phase,
                   double warm)
    {
        m_warm = warm;
        m_src = src;
        m_dst = dst;
        m_ipBytes = ipPktBytes;
        m_rate = std::move(rateKbps);
        m_t0 = t0;
        m_T = T;
        m_phase = phase;
    }

  private:
    void StartApplication() override
    {
        m_socket = Socket::CreateSocket(GetNode(), UdpSocketFactory::GetTypeId());
        // Bind to a fixed source address so a reroute does not change the flow's 5-tuple.
        m_socket->Bind(InetSocketAddress(m_src, 0));
        m_socket->Connect(InetSocketAddress(m_dst, kPort));
        // FirstWake() is relative to t0; Schedule() is relative to now.
        double first = (m_t0 - Simulator::Now().GetSeconds()) + FirstWake();
        m_ev = Simulator::Schedule(Seconds(std::max(first, 0.0)), &TmSource::Tick, this);
    }

    void StopApplication() override
    {
        Simulator::Cancel(m_ev);
        if (m_socket)
        {
            m_socket->Close();
        }
    }

    double Gap(int idx) const
    {
        double r = m_rate[idx];
        return (r > 0) ? (m_ipBytes * 8.0) / (r * 1000.0) : 0.0;
    }

    // time (relative to now) of the first packet of the first non-zero interval
    double FirstWake() const
    {
        if (m_rate[0] > 0)
        {
            // warm-up: interval-0 rate runs for m_warm seconds before t0 so that the
            // measured interval 0 is not biased by the pipe filling up
            return -m_warm + m_phase * std::min(Gap(0), m_warm);
        }
        for (size_t i = 1; i < m_rate.size(); ++i)
        {
            if (m_rate[i] > 0)
            {
                return i * m_T + m_phase * std::min(Gap(i), m_T);
            }
        }
        return 0.0;
    }

    void Tick()
    {
        double now = Simulator::Now().GetSeconds() - m_t0;
        int idx = (now < 0) ? 0 : static_cast<int>(std::floor(now / m_T + 1e-12));
        if (idx >= static_cast<int>(m_rate.size()))
        {
            return;
        }
        if (m_rate[idx] <= 0)
        {
            // idle: wake at the next interval that has traffic
            for (size_t j = idx + 1; j < m_rate.size(); ++j)
            {
                if (m_rate[j] > 0)
                {
                    double at = j * m_T + m_phase * std::min(Gap(j), m_T) - now;
                    m_ev = Simulator::Schedule(Seconds(std::max(at, 1e-9)), &TmSource::Tick, this);
                    return;
                }
            }
            return;
        }
        m_socket->Send(Create<Packet>(m_ipBytes - 28));  // 20 B IP + 8 B UDP
        m_ev = Simulator::Schedule(Seconds(Gap(idx)), &TmSource::Tick, this);
    }

    Ptr<Socket> m_socket;
    Ipv4Address m_src;
    Ipv4Address m_dst;
    uint32_t m_ipBytes = 1250;
    std::vector<double> m_rate;
    double m_t0 = 0;
    double m_T = 1;
    double m_phase = 0;
    double m_warm = 0;
    EventId m_ev;
};

// ------------------------------------------------------------------ traces
void
OnPhyTxEnd(uint32_t li, uint32_t dir, Ptr<const Packet> p)
{
    double rel = Simulator::Now().GetSeconds() - g.t0;
    if (rel < 0)
    {
        return;
    }
    int idx = static_cast<int>(std::floor(rel / g.T));
    if (idx >= 0 && idx < static_cast<int>(g.nInt))
    {
        g.linkBytes[li][dir][idx] += p->GetSize();
    }
}

void
FailLink(uint32_t li, double rerouteDelayS)
{
    Link& L = g.links[li];
    L.up = false;
    g.nodes.Get(L.u)->GetObject<Ipv4>()->SetDown(L.ifU);
    g.nodes.Get(L.v)->GetObject<Ipv4>()->SetDown(L.ifV);
    std::cout << "[t=" << Simulator::Now().GetSeconds() << "s] link " << L.u << "-" << L.v
              << " DOWN (interval " << g.currentInterval << ")\n";
    Simulator::Schedule(Seconds(rerouteDelayS), []() {
        std::cout << "[t=" << Simulator::Now().GetSeconds() << "s] rerouting after failure\n";
        ApplyPlan(static_cast<uint32_t>(g.currentInterval), false);
    });
}

void
BoundaryUpdate(uint32_t i)
{
    ApplyPlan(i, true);
}

double
Percentile(const std::vector<uint64_t>& counts, double binWidthS, double p)
{
    uint64_t total = 0;
    for (auto c : counts)
    {
        total += c;
    }
    if (total == 0)
    {
        return 0.0;
    }
    uint64_t target = static_cast<uint64_t>(std::ceil(p * total));
    uint64_t cum = 0;
    for (size_t i = 0; i < counts.size(); ++i)
    {
        cum += counts[i];
        if (cum >= target)
        {
            return (i + 1) * binWidthS * 1000.0;  // upper bin edge, ms
        }
    }
    return counts.size() * binWidthS * 1000.0;
}
}  // namespace

// ====================================================================== main
int
main(int argc, char* argv[])
{
    std::string linksFile = "ns3_input/geant_sim_links.csv";
    std::string traceFile = "ns3_input/tm_trace.csv";
    std::string outDir = "ns3_out";
    std::string tag = "run";
    std::string mode = "static";
    std::string delayModel = "geo";
    std::string failSpec;
    std::string routeLogFile;
    double intervalSec = 0.25;
    double capScale = 1.0;
    double demandScale = 1.0;
    double uniformDelayMs = 5.0;
    double failAt = 0.5;
    double failRerouteMs = 50.0;
    double drain = 0.5;
    double warm = 0.1;
    double beta = 100.0;
    double trigger = 0.55;
    double hyst = 0.05;
    double minFlow = 50.0;
    uint32_t nIntervals = 8;
    uint32_t pktBytes = 1250;
    uint32_t queuePkts = 100;
    uint32_t seed = 1;
    uint32_t run = 1;
    int iters = 4;
    int pcapNode = -1;
    bool writeXml = true;
    bool planOnly = false;

    CommandLine cmd(__FILE__);
    cmd.AddValue("links", "geant_sim_links.csv from export_ns3_trace.py", linksFile);
    cmd.AddValue("trace", "tm_trace.csv from export_ns3_trace.py", traceFile);
    cmd.AddValue("out", "output directory (must exist)", outDir);
    cmd.AddValue("tag", "scenario tag used in output file names", tag);
    cmd.AddValue("mode", "static | reactive | proactive | oracle", mode);
    cmd.AddValue("intervals", "number of matrix intervals to replay", nIntervals);
    cmd.AddValue("interval-sec", "simulated seconds per matrix interval", intervalSec);
    cmd.AddValue("cap-scale", "multiply every link capacity (stress test <1)", capScale);
    cmd.AddValue("demand-scale", "multiply every demand", demandScale);
    cmd.AddValue("delay-model", "geo (per-link) | uniform", delayModel);
    cmd.AddValue("uniform-delay-ms", "delay when --delay-model=uniform", uniformDelayMs);
    cmd.AddValue("pkt", "IP packet size in bytes", pktBytes);
    cmd.AddValue("queue-pkts", "device queue size in packets", queuePkts);
    cmd.AddValue("min-flow-kbps", "skip OD flows below this rate per interval", minFlow);
    cmd.AddValue("beta", "load penalty in w = igp*(1+beta*util^2)", beta);
    cmd.AddValue("trigger", "act only if the controller expects peak utilisation above this", trigger);
    cmd.AddValue("hysteresis", "keep the previous plan unless the new one cuts estimated overflow by more than this fraction", hyst);
    cmd.AddValue("te-iters", "successive-averaging rounds for load-aware routing", iters);
    cmd.AddValue("seed", "RNG seed (flow phase offsets only)", seed);
    cmd.AddValue("run", "RNG run number", run);
    cmd.AddValue("warmup", "seconds of interval-0 traffic before measurement starts", warm);
    cmd.AddValue("drain", "seconds to keep simulating after the last interval", drain);
    cmd.AddValue("fail", "link to take down, e.g. 9-16 (default: none)", failSpec);
    cmd.AddValue("fail-at", "seconds after traffic start at which --fail happens", failAt);
    cmd.AddValue("fail-reroute-ms", "ms until routes are recomputed after a failure", failRerouteMs);
    cmd.AddValue("route-log", "write every OD path per interval to this CSV", routeLogFile);
    cmd.AddValue("pcap-node", "enable pcap on all devices of this node", pcapNode);
    cmd.AddValue("xml", "write the FlowMonitor XML", writeXml);
    cmd.AddValue("plan-only", "no packet simulation: evaluate every controller's plan against the true load for all intervals", planOnly);
    cmd.Parse(argc, argv);

    if (mode != "static" && mode != "reactive" && mode != "proactive" && mode != "oracle")
    {
        std::cerr << "--mode must be static, reactive, proactive or oracle\n";
        return 1;
    }
    RngSeedManager::SetSeed(seed);
    RngSeedManager::SetRun(run);

    g.mode = mode;
    g.T = intervalSec;
    g.beta = beta;
    g.trigger = trigger;
    g.hyst = hyst;
    g.minFlowKbps = minFlow;
    g.demandScale = demandScale;
    g.iters = iters;

    // ---- topology
    auto linkRows = ReadCsv(linksFile);
    g.adj.assign(kN, {});
    for (const auto& f : linkRows)
    {
        if (f.size() < 8)
        {
            continue;
        }
        Link L;
        L.u = std::stoul(f[0]);
        L.v = std::stoul(f[1]);
        L.capKbps = std::stod(f[4]) * capScale;
        L.igp = std::stod(f[5]);
        L.delayMs = (delayModel == "uniform") ? uniformDelayMs : std::stod(f[7]);
        int li = static_cast<int>(g.links.size());
        g.links.push_back(L);
        g.adj[L.u].push_back({li, static_cast<int>(L.v)});
        g.adj[L.v].push_back({li, static_cast<int>(L.u)});
    }
    std::cout << "Links: " << g.links.size() << "  mode=" << mode << "  cap-scale=" << capScale
              << "  delay-model=" << delayModel << "\n";

    // ---- traffic trace
    auto traceRows = ReadCsv(traceFile);
    uint32_t avail = 0;
    for (const auto& f : traceRows)
    {
        if (f.size() >= 5)
        {
            avail = std::max<uint32_t>(avail, std::stoul(f[0]) + 1);
        }
    }
    g.nInt = std::min(nIntervals, avail);
    g.tr.assign(g.nInt, ZeroMatrix());
    g.fc.assign(g.nInt, ZeroMatrix());
    g.ob.assign(g.nInt, ZeroMatrix());
    for (const auto& f : traceRows)
    {
        if (f.size() < 5)
        {
            continue;
        }
        uint32_t i = std::stoul(f[0]);
        if (i >= g.nInt)
        {
            continue;
        }
        uint32_t s = std::stoul(f[2]);
        uint32_t d = std::stoul(f[3]);
        double kbps = std::stod(f[4]) * demandScale;
        Matrix* M = (f[1] == "true") ? &g.tr[i] : (f[1] == "forecast") ? &g.fc[i] : &g.ob[i];
        (*M)[s][d] = kbps;
    }
    g.estIgp.assign(g.nInt, 0);
    g.estChosen.assign(g.nInt, 0);
    g.routeChanges.assign(g.nInt, 0);
    g.stretchNum.assign(g.nInt, 0);
    g.stretchDen.assign(g.nInt, 0);
    g.offeredKbps.assign(g.nInt, 0);
    g.prevPath.assign(kN, std::vector<std::vector<int>>(kN));

    if (planOnly)
    {
        // Same controller code, no packets: for each interval evaluate the plan each controller
        // would pick (using ITS view of demand) against the TRUE demand of that interval.
        std::ofstream po(outDir + "/" + tag + "_planonly.csv");
        po << "interval,static,reactive,proactive,oracle,chg_reactive,chg_proactive,chg_oracle\n";
        std::vector<std::vector<double>> pk(4, std::vector<double>(g.nInt, 0.0));
        std::vector<std::vector<double>> chg(4, std::vector<double>(g.nInt, 0.0));
        const char* modes[4] = {"static", "reactive", "proactive", "oracle"};
        for (int m = 0; m < 4; ++m)
        {
            g.mode = modes[m];
            g.havePrevPlan = false;
            Plan prev;
            for (uint32_t i = 0; i < g.nInt; ++i)
            {
                Plan p = BuildPlan(ControlMatrix(i));
                g.prevPlan = p;
                g.havePrevPlan = true;
                pk[m][i] = EstPeak(p, g.tr[i]);
                if (i > 0)
                {
                    for (uint32_t d = 0; d < kN; ++d)
                    {
                        for (uint32_t n = 0; n < kN; ++n)
                        {
                            if (n != d && p.nh[d][n] != prev.nh[d][n])
                            {
                                chg[m][i] += 1;
                            }
                        }
                    }
                }
                prev = p;
            }
        }
        double mean[4] = {0, 0, 0, 0};
        for (uint32_t i = 0; i < g.nInt; ++i)
        {
            po << i;
            for (int m = 0; m < 4; ++m)
            {
                po << "," << pk[m][i];
                mean[m] += pk[m][i] / g.nInt;
            }
            po << "," << chg[1][i] << "," << chg[2][i] << "," << chg[3][i] << "\n";
        }
        std::cout << std::fixed << std::setprecision(4) << "plan-only mean peak util over " << g.nInt
                  << " intervals (cap-scale " << capScale << "): static " << mean[0] << "  reactive " << mean[1]
                  << "  proactive " << mean[2] << "  oracle " << mean[3] << "\n";
        return 0;
    }

    // ---- network
    g.nodes.Create(kN);
    InternetStackHelper internet;
    internet.Install(g.nodes);

    Ipv4AddressHelper address;
    address.SetBase("10.1.0.0", "255.255.255.252");
    g.linkBytes.resize(g.links.size());
    for (size_t li = 0; li < g.links.size(); ++li)
    {
        Link& L = g.links[li];
        for (int dir = 0; dir < 2; ++dir)
        {
            g.linkBytes[li][dir].assign(g.nInt, 0.0);
        }
        PointToPointHelper p2p;
        p2p.SetDeviceAttribute("DataRate",
                               DataRateValue(DataRate(static_cast<uint64_t>(L.capKbps * 1000.0))));
        p2p.SetChannelAttribute("Delay", TimeValue(MicroSeconds(L.delayMs * 1000.0)));
        p2p.SetQueue("ns3::DropTailQueue<Packet>",
                     "MaxSize",
                     StringValue(std::to_string(queuePkts) + "p"));
        NetDeviceContainer devs = p2p.Install(g.nodes.Get(L.u), g.nodes.Get(L.v));
        Ipv4InterfaceContainer ifs = address.Assign(devs);
        address.NewNetwork();
        // Ipv4AddressHelper::Assign silently installs a default FqCoDel queue disc; remove it so
        // each router port is a plain DropTail FIFO of --queue-pkts packets.
        TrafficControlHelper tch;
        tch.Uninstall(devs);
        if (li == 0)
        {
            Ptr<TrafficControlLayer> tc = g.nodes.Get(L.u)->GetObject<TrafficControlLayer>();
            std::cout << "Queue discipline on link 0: "
                      << (tc->GetRootQueueDiscOnDevice(devs.Get(0)) ? "queue disc present (unexpected)"
                                                                     : "none (DropTail device queue)")
                      << ", " << queuePkts << " packets\n";
        }
        L.ifU = g.nodes.Get(L.u)->GetObject<Ipv4>()->GetInterfaceForDevice(devs.Get(0));
        L.ifV = g.nodes.Get(L.v)->GetObject<Ipv4>()->GetInterfaceForDevice(devs.Get(1));
        L.addrU = ifs.GetAddress(0);
        L.addrV = ifs.GetAddress(1);
        for (int dir = 0; dir < 2; ++dir)
        {
            Ptr<NetDevice> nd = devs.Get(dir);
            nd->TraceConnectWithoutContext(
                "PhyTxEnd",
                MakeBoundCallback(&OnPhyTxEnd, static_cast<uint32_t>(li), static_cast<uint32_t>(dir)));
        }
        if (pcapNode >= 0 && static_cast<int>(L.u) == pcapNode)
        {
            p2p.EnablePcap(outDir + "/" + tag + "_" + mode + "_pcap", devs.Get(0), false);
        }
        if (pcapNode >= 0 && static_cast<int>(L.v) == pcapNode)
        {
            p2p.EnablePcap(outDir + "/" + tag + "_" + mode + "_pcap", devs.Get(1), false);
        }
    }
    g.destAddr.resize(kN);
    for (uint32_t n = 0; n < kN; ++n)
    {
        g.destAddr[n] = g.nodes.Get(n)->GetObject<Ipv4>()->GetAddress(1, 0).GetLocal();
    }

    // ---- sinks (one per node) and sources (one per OD pair)
    double trafficEnd = g.t0 + g.nInt * g.T;
    for (uint32_t d = 0; d < kN; ++d)
    {
        PacketSinkHelper sink("ns3::UdpSocketFactory", InetSocketAddress(Ipv4Address::GetAny(), kPort));
        ApplicationContainer a = sink.Install(g.nodes.Get(d));
        a.Start(Seconds(0.0));
        a.Stop(Seconds(trafficEnd + drain));
    }
    uint32_t nFlows = 0;
    double offeredTotal = 0;
    double skippedTotal = 0;
    for (uint32_t s = 0; s < kN; ++s)
    {
        for (uint32_t d = 0; d < kN; ++d)
        {
            if (s == d)
            {
                continue;
            }
            std::vector<double> rates(g.nInt, 0.0);
            bool any = false;
            for (uint32_t i = 0; i < g.nInt; ++i)
            {
                double r = g.tr[i][s][d];
                offeredTotal += r;
                if (r >= minFlow)
                {
                    rates[i] = r;
                    g.offeredKbps[i] += r;
                    any = true;
                }
                else
                {
                    skippedTotal += r;
                }
            }
            if (!any)
            {
                continue;
            }
            Ptr<UniformRandomVariable> rv = CreateObject<UniformRandomVariable>();
            rv->SetStream(1000 + s * kN + d);
            Ptr<TmSource> app = CreateObject<TmSource>();
            app->Configure(g.destAddr[s], g.destAddr[d], pktBytes, rates, g.t0, g.T, rv->GetValue(0.0, 1.0), warm);
            g.nodes.Get(s)->AddApplication(app);
            app->SetStartTime(Seconds(std::max(0.0, g.t0 - warm - 0.2)));  // sockets ready before first packet
            app->SetStopTime(Seconds(trafficEnd));
            ++nFlows;
        }
    }
    std::cout << "OD flows: " << nFlows << "  skipped demand (below " << minFlow
              << " kbps): " << std::fixed << std::setprecision(4)
              << (offeredTotal > 0 ? 100.0 * skippedTotal / offeredTotal : 0.0) << " %\n";

    // ---- routing
    if (!routeLogFile.empty())
    {
        g.routeLog.open(routeLogFile);
        g.routeLog << "interval,src,dst,path\n";
    }
    ApplyPlan(0, true);
    for (uint32_t i = 1; i < g.nInt; ++i)
    {
        Simulator::Schedule(Seconds(g.t0 + i * g.T), &BoundaryUpdate, i);
    }
    if (!failSpec.empty())
    {
        uint32_t a = 0;
        uint32_t b = 0;
        char dash;
        std::stringstream ss(failSpec);
        ss >> a >> dash >> b;
        int found = -1;
        for (size_t li = 0; li < g.links.size(); ++li)
        {
            if ((g.links[li].u == a && g.links[li].v == b) || (g.links[li].u == b && g.links[li].v == a))
            {
                found = static_cast<int>(li);
            }
        }
        if (found < 0)
        {
            std::cerr << "No link " << failSpec << "\n";
            return 1;
        }
        Simulator::Schedule(Seconds(g.t0 + failAt), &FailLink, static_cast<uint32_t>(found), failRerouteMs / 1000.0);
    }

    // ---- monitor
    FlowMonitorHelper fmh;
    fmh.SetMonitorAttribute("DelayBinWidth", DoubleValue(0.0005));
    fmh.SetMonitorAttribute("JitterBinWidth", DoubleValue(0.0005));
    Ptr<FlowMonitor> monitor = fmh.InstallAll();

    Simulator::Stop(Seconds(trafficEnd + drain));
    std::cout << "Running " << g.nInt << " intervals x " << g.T << " s ...\n";
    Simulator::Run();
    monitor->CheckForLostPackets();

    // ---- results
    uint64_t tx = 0;
    uint64_t rx = 0;
    double delaySum = 0;
    double jitterSum = 0;
    uint64_t jitterN = 0;
    double excessSum = 0;
    uint64_t dropNoRoute = 0;
    uint64_t dropIfDown = 0;
    uint64_t dropTtl = 0;
    uint64_t dropQueue = 0;
    std::vector<uint64_t> hist;
    for (const auto& kv : monitor->GetFlowStats())
    {
        const FlowMonitor::FlowStats& st = kv.second;
        tx += st.txPackets;
        rx += st.rxPackets;
        delaySum += st.delaySum.GetSeconds();
        if (st.rxPackets > 1)
        {
            jitterSum += st.jitterSum.GetSeconds();
            jitterN += st.rxPackets - 1;
        }
        if (st.rxPackets > 0)
        {
            excessSum += st.delaySum.GetSeconds() - st.minDelay.GetSeconds() * st.rxPackets;
        }
        auto drops = [&](uint32_t reason) -> uint64_t {
            return reason < st.packetsDropped.size() ? st.packetsDropped[reason] : 0;
        };
        dropNoRoute += drops(Ipv4FlowProbe::DROP_NO_ROUTE);
        dropTtl += drops(Ipv4FlowProbe::DROP_TTL_EXPIRE);
        dropIfDown += drops(Ipv4FlowProbe::DROP_INTERFACE_DOWN);
        dropQueue += drops(Ipv4FlowProbe::DROP_QUEUE) + drops(Ipv4FlowProbe::DROP_QUEUE_DISC);
        const Histogram& h = st.delayHistogram;
        if (hist.size() < h.GetNBins())
        {
            hist.resize(h.GetNBins(), 0);
        }
        for (uint32_t b = 0; b < h.GetNBins(); ++b)
        {
            hist[b] += h.GetBinCount(b);
        }
    }
    uint64_t lost = tx > rx ? tx - rx : 0;

    // per-interval link utilisation
    std::vector<double> peak(g.nInt, 0.0);
    std::vector<int> peakLink(g.nInt, -1);
    std::ofstream linkCsv(outDir + "/" + tag + "_" + mode + ".links.csv");
    linkCsv << "interval,u,v,util_fwd,util_rev\n";
    for (uint32_t i = 0; i < g.nInt; ++i)
    {
        for (size_t li = 0; li < g.links.size(); ++li)
        {
            double cap = g.links[li].capKbps * 1000.0 * g.T;  // bits per interval
            double uf = g.linkBytes[li][0][i] * 8.0 / cap;
            double ur = g.linkBytes[li][1][i] * 8.0 / cap;
            linkCsv << i << "," << g.links[li].u << "," << g.links[li].v << "," << uf << "," << ur << "\n";
            double m = std::max(uf, ur);
            if (m > peak[i])
            {
                peak[i] = m;
                peakLink[i] = static_cast<int>(li);
            }
        }
    }
    std::ofstream ivCsv(outDir + "/" + tag + "_" + mode + ".intervals.csv");
    ivCsv << "interval,offered_Gbps,peak_util,peak_link,route_changes,igp_stretch,est_peak_igp,est_peak_chosen\n";
    double sumPeak = 0;
    double sumChanges = 0;
    double sNum = 0;
    double sDen = 0;
    int gt70 = 0;
    int gt95 = 0;
    for (uint32_t i = 0; i < g.nInt; ++i)
    {
        sumPeak += peak[i];
        sumChanges += (i > 0) ? g.routeChanges[i] : 0;
        sNum += g.stretchNum[i];
        sDen += g.stretchDen[i];
        gt70 += peak[i] > 0.70;
        gt95 += peak[i] > 0.95;
        int pl = peakLink[i];
        ivCsv << i << "," << g.offeredKbps[i] / 1e6 << "," << peak[i] << ","
              << (pl >= 0 ? std::to_string(g.links[pl].u) + "-" + std::to_string(g.links[pl].v) : "-")
              << "," << g.routeChanges[i] << ","
              << (g.stretchDen[i] > 0 ? g.stretchNum[i] / g.stretchDen[i] : 1.0) << "," << g.estIgp[i] << ","
              << g.estChosen[i] << "\n";
    }
    std::vector<double> sortedPeak = peak;
    std::sort(sortedPeak.begin(), sortedPeak.end());
    double p95Peak = sortedPeak[std::min<size_t>(sortedPeak.size() - 1, std::ceil(0.95 * sortedPeak.size()) - 1)];

    double meanDelayMs = rx ? 1000.0 * delaySum / rx : 0.0;
    double meanJitterMs = jitterN ? 1000.0 * jitterSum / jitterN : 0.0;
    double meanExcessMs = rx ? 1000.0 * excessSum / rx : 0.0;
    double lossPct = tx ? 100.0 * lost / tx : 0.0;

    std::ofstream sum(outDir + "/" + tag + "_" + mode + ".summary.csv");
    sum << "tag,mode,cap_scale,demand_scale,delay_model,intervals,interval_sec,seed,fail,"
           "tx_pkts,rx_pkts,lost_pkts,loss_pct,mean_delay_ms,mean_excess_delay_ms,p50_ms,p95_ms,p99_ms,"
           "mean_jitter_ms,mean_peak_util,p95_peak_util,max_peak_util,intervals_peak_gt70,"
           "intervals_peak_gt95,drop_no_route,drop_iface_down,drop_ttl,"
           "route_changes_per_interval,igp_stretch\n";
    sum << tag << "," << mode << "," << capScale << "," << demandScale << "," << delayModel << "," << g.nInt
        << "," << g.T << "," << seed << "," << (failSpec.empty() ? "none" : failSpec) << "," << tx << ","
        << rx << "," << lost << "," << lossPct << "," << meanDelayMs << "," << meanExcessMs << ","
        << Percentile(hist, 0.0005, 0.50) << "," << Percentile(hist, 0.0005, 0.95) << ","
        << Percentile(hist, 0.0005, 0.99) << "," << meanJitterMs << "," << sumPeak / g.nInt << ","
        << p95Peak << "," << sortedPeak.back() << "," << gt70 << "," << gt95 << ","
        << dropNoRoute << "," << dropIfDown << "," << dropTtl << ","
        << (g.nInt > 1 ? sumChanges / (g.nInt - 1) : 0.0) << "," << (sDen > 0 ? sNum / sDen : 1.0) << "\n";

    if (writeXml)
    {
        monitor->SerializeToXmlFile(outDir + "/" + tag + "_" + mode + ".flowmon.xml", false, false);
    }

    std::cout << std::fixed << std::setprecision(3) << "tx=" << tx << " rx=" << rx << " lost=" << lost << " ("
              << lossPct << "%)  mean delay " << meanDelayMs << " ms  p99 " << Percentile(hist, 0.0005, 0.99)
              << " ms  mean peak util " << sumPeak / g.nInt << "  route changes/interval "
              << (g.nInt > 1 ? sumChanges / (g.nInt - 1) : 0.0) << "  stretch "
              << (sDen > 0 ? sNum / sDen : 1.0) << "\n";
    Simulator::Destroy();
    return 0;
}
