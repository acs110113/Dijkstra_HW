// solver.cpp -- modified from dijkstra_foundation.cpp
//
// Foundation Dijkstra implementation for the Shortest-Path Competition.
//
// Students must build their solver by modifying and extending this file.
// The authoritative description of the formats and the rules is README.md.
//
// Usage:
//     ./solver <graph_file> <query_file> <output_file>
//
// File formats (0-based vertex indices):
//
//   <graph_file>
//     V E FLAGS
//     u_1 v_1 w_1
//     ...
//     u_E v_E w_E
//     [ if FLAGS has bit 0 set:
//       x_0 y_0
//       ...
//       x_{V-1} y_{V-1}
//     ]
//
//   FLAGS is a bitmask:
//     bit 0 (value 1) — the coordinate block is present
//     bit 1 (value 2) — the edge list is DIRECTED: "u v w" is the arc u -> v
//                       only. When the bit is clear the graph is undirected and
//                       each line contributes both u -> v and v -> u.
//   A FLAGS value of 0 or 1 therefore means exactly what HAS_COORDS used to.
//
//   Coordinates are integers in the v2 datasets (they are still read as
//   floating point here, so both integer and decimal text parse correctly).
//
//   <query_file>
//     Q
//     s_1 t_1
//     ...
//     s_Q t_Q
//
//   <output_file>
//     d_1
//     ...
//     d_Q                 (-1 if t_i unreachable from s_i)

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <queue>
#include <vector>
#include <limits>
#include <utility>
#include <functional>
#ifdef PROFILE
#include <chrono>
#endif

using std::vector;

struct Edge {
    int32_t to;
    int64_t w;
};

static const int32_t FLAG_COORDS   = 1;
static const int32_t FLAG_DIRECTED = 2;

static int32_t V = 0;
static int32_t E = 0;
static int32_t FLAGS = 0;
static vector<vector<Edge>> adj;
static vector<double> coord_x, coord_y;

// Buffered standard-library input; retain the foundation file format.
class GraphInput {
    std::FILE* f;
    char buffer[1<<16]; size_t pos=0,len=0;
    int get() {
        if(pos==len) {len=std::fread(buffer,1,sizeof(buffer),f);pos=0;if(!len)return EOF;}
        return static_cast<unsigned char>(buffer[pos++]);
    }
public:
    explicit GraphInput(std::FILE* file):f(file) {}
    bool integer(int32_t& result) {
        int c; do {c=get();} while(c!=EOF && c<=32);
        if(c==EOF) return false;
        bool negative=c=='-'; if(negative || c=='+') c=get();
        int64_t value=0; bool digits=false;
        while(c>='0' && c<='9') {digits=true;value=value*10+c-'0';c=get();}
        result=static_cast<int32_t>(negative?-value:value);return digits;
    }
    bool real(double& result) {
        int c; do {c=get();} while(c!=EOF && c<=32);
        if(c==EOF) return false;
        char text[128]; size_t n=0;
        while(c!=EOF && c>32) {if(n+1>=sizeof(text))return false;text[n++]=char(c);c=get();}
        text[n]=0; char* end=nullptr; result=std::strtod(text,&end);return end==text+n;
    }
};

static void read_graph(const char* path) {
    std::FILE* f = std::fopen(path, "r");
    if (!f) { std::fprintf(stderr, "cannot open graph file: %s\n", path); std::exit(1); }

    GraphInput input(f);
    if (!input.integer(V) || !input.integer(E) || !input.integer(FLAGS)) {
        std::fprintf(stderr, "bad graph header\n"); std::exit(1);
    }
    const bool directed = (FLAGS & FLAG_DIRECTED) != 0;
    adj.assign(V, {});
    for (int32_t i = 0; i < E; ++i) {
        int32_t u, v, w;
        if (!input.integer(u) || !input.integer(v) || !input.integer(w)) {
            std::fprintf(stderr, "bad edge at line %d\n", i + 2); std::exit(1);
        }
        adj[u].push_back({v, w});
        if (!directed) adj[v].push_back({u, w});
    }
    if (FLAGS & FLAG_COORDS) {
        coord_x.resize(V);
        coord_y.resize(V);
        for (int32_t i = 0; i < V; ++i) {
            if (!input.real(coord_x[i]) || !input.real(coord_y[i])) {
                std::fprintf(stderr, "bad coords at vertex %d\n", i); std::exit(1);
            }
        }
    }
    std::fclose(f);
}


// Exact contraction hierarchy, computed exclusively from the input graph.
// The foundation adjacency lists and Dijkstra relaxation are retained. During
// preprocessing, eliminating v adds u->w with length (u->v)+(v->w), unless
// a bounded Dijkstra witness proves an equally short path avoiding v.
// A search limit only adds redundant shortcuts; it cannot lose a shortest path.
static const int64_t INF = std::numeric_limits<int64_t>::max()/4;
using PQItem = std::pair<int64_t,int32_t>;
using Heap = std::priority_queue<PQItem,vector<PQItem>,std::greater<PQItem>>;
struct ReusableHeap : Heap {
    void clear() { this->c.clear(); }
};
static vector<vector<Edge>> radj, up, back;
static vector<int32_t> rank_id, level, removed_neighbors;
static vector<int64_t> wd;
static vector<uint32_t> ws;
static vector<uint32_t> target_stamp;
static vector<int64_t> target_limit;
static bool plain_bidirectional=false;
static uint32_t epoch=0;
struct Shortcut { int32_t from,to; int64_t w; };

static void new_epoch(vector<uint32_t>& stamps,uint32_t& e) {
    if (++e==0) { std::fill(stamps.begin(),stamps.end(),0); e=1; }
}

static void find_shortcuts(int32_t v,vector<Shortcut>& shortcuts) {
    shortcuts.clear();
    static ReusableHeap pq;
    // At low degree even retaining every shortcut cannot increase the live
    // edge count. Avoid a potentially long witness search in this case.
    if(adj[v].size()*radj[v].size()<=adj[v].size()+radj[v].size()) {
        for(const Edge& a:radj[v]) for(const Edge& b:adj[v]) if(a.to!=b.to) {
            int64_t nd=a.w+b.w; bool covered=false;
            for(const Edge& e:adj[a.to]) if(e.to==b.to && e.w<=nd) {covered=true;break;}
            if(!covered) shortcuts.push_back({a.to,b.to,nd});
        }
        return;
    }
    for (const Edge& a:radj[v]) {
        int32_t s=a.to;
        int64_t limit=0;
        for(const Edge& b:adj[v]) if(b.to!=s) limit=std::max(limit,a.w+b.w);
        new_epoch(ws,epoch);
        if(epoch==1) std::fill(target_stamp.begin(),target_stamp.end(),0);
        int remaining=0;
        for(const Edge& b:adj[v]) if(b.to!=s) {
            target_stamp[b.to]=epoch; target_limit[b.to]=a.w+b.w; ++remaining;
        }
        pq.clear();
        wd[s]=0; ws[s]=epoch; pq.push({0,s});
        int settled=0;
        while(!pq.empty() && settled<160 && remaining) {
            auto [d,u]=pq.top(); pq.pop();
            if(d!=wd[u]) continue;
            if(d>limit) break;
            ++settled;
            for(const Edge& e:adj[u]) {
                if(e.to==v) continue;
                int64_t nd=d+e.w;
                if(nd>limit) continue;
                if(ws[e.to]!=epoch || nd<wd[e.to]) {
                    ws[e.to]=epoch; wd[e.to]=nd; pq.push({nd,e.to});
                    if(target_stamp[e.to]==epoch && nd<=target_limit[e.to]) {
                        target_stamp[e.to]=0; --remaining;
                        if(target_limit[e.to]==limit) {
                            limit=0;
                            for(const Edge& target:adj[v])
                                if(target_stamp[target.to]==epoch)
                                    limit=std::max(limit,target_limit[target.to]);
                        }
                    }
                }
            }
        }
        for(const Edge& b:adj[v]) if(b.to!=s) {
            int64_t nd=a.w+b.w;
            if(ws[b.to]!=epoch || wd[b.to]>nd) shortcuts.push_back({s,b.to,nd});
        }
    }
}

static void add_arc(int32_t u,int32_t v,int64_t w) {
    for(Edge& e:adj[u]) if(e.to==v) {
        if(w>=e.w) return;
        e.w=w;
        for(Edge& r:radj[v]) if(r.to==u) { r.w=w; break; }
        return;
    }
    adj[u].push_back({v,w}); radj[v].push_back({u,w});
}


// Version 2: exploit the symmetry of undirected inputs throughout contraction.
// Each unordered neighbor pair needs one witness, not two identical searches.
// The original directed implementation below remains available unchanged.
static bool symmetric_hierarchy=false;
static uint64_t witness_calls=0, witness_caps=0, witness_scans=0;
static uint64_t priority_checks=0, priority_requeues=0;
static uint64_t shortcuts_added=0, pruned_arcs=0;

static void erase_neighbor(vector<Edge>& es,int32_t v) {
    for(size_t i=0;i<es.size();++i) if(es[i].to==v) {
        es[i]=es.back(); es.pop_back(); return;
    }
}

static void add_undirected_edge(int32_t u,int32_t v,int64_t w) {
    for(Edge& e:adj[u]) if(e.to==v) {
        if(e.w<=w) return;
        e.w=w;
        for(Edge& r:adj[v]) if(r.to==u) {r.w=w;return;}
    }
    adj[u].push_back({v,w}); adj[v].push_back({u,w});
    ++shortcuts_added;
}

static void symmetric_shortcuts(int32_t v, vector<Shortcut>& candidates,
                               ReusableHeap& pq) {
    candidates.clear();
    const auto& neighbors=adj[v];
    const size_t degree=neighbors.size();
    if(degree<2) return;
    if(degree==2) {
        const Edge a=neighbors[0],b=neighbors[1];
        const int64_t sum=a.w+b.w;
        for(const Edge& e:adj[a.to]) if(e.to==b.to && e.w<=sum) return;
        candidates.push_back({a.to,b.to,sum});
        return;
    }
    // More witness work at high degree can prevent a much larger fill later.
    // Hitting either bound retains uncertain shortcuts, preserving exactness.
    const size_t settle_limit=std::min<size_t>(2048,160+24*degree);
    const size_t scan_limit=std::max<size_t>(8192,settle_limit*48);
    for(size_t i=0;i+1<degree;++i) {
        const Edge a=neighbors[i];
        new_epoch(ws,epoch);
        if(epoch==1) std::fill(target_stamp.begin(),target_stamp.end(),0);
        int remaining=0;
        int64_t limit=0;
        for(size_t j=i+1;j<degree;++j) {
            const Edge b=neighbors[j];
            target_stamp[b.to]=epoch;target_limit[b.to]=a.w+b.w;
            limit=std::max(limit,a.w+b.w);++remaining;
        }
        pq.clear();ws[a.to]=epoch;wd[a.to]=0;pq.push({0,a.to});
        size_t settled=0,scans=0;
        ++witness_calls;
        while(!pq.empty() && remaining && settled<settle_limit && scans<scan_limit) {
            auto [d,u]=pq.top();pq.pop();
            if(d!=wd[u]) continue;
            if(d>limit) break;
            ++settled;
            for(const Edge& e:adj[u]) {
                if(++scans>scan_limit) break;
                if(e.to==v) continue;
                const int64_t nd=d+e.w;
                if(nd>limit) continue;
                if(ws[e.to]!=epoch || nd<wd[e.to]) {
                    ws[e.to]=epoch;wd[e.to]=nd;pq.push({nd,e.to});
                    if(target_stamp[e.to]==epoch && nd<=target_limit[e.to]) {
                        target_stamp[e.to]=0;--remaining;
                        if(target_limit[e.to]==limit) {
                            limit=0;
                            for(size_t j=i+1;j<degree;++j) {
                                int32_t target=neighbors[j].to;
                                if(target_stamp[target]==epoch)
                                    limit=std::max(limit,target_limit[target]);
                            }
                        }
                    }
                }
            }
        }
        witness_scans+=scans;
        if(remaining && (settled>=settle_limit || scans>=scan_limit)) ++witness_caps;
        for(size_t j=i+1;j<degree;++j) {
            const Edge b=neighbors[j];const int64_t sum=a.w+b.w;
            if(ws[b.to]!=epoch || wd[b.to]>sum) candidates.push_back({a.to,b.to,sum});
        }
    }
}

static void prepare_undirected() {
    symmetric_hierarchy=true;
    up.resize(V); rank_id.assign(V,-1);level.assign(V,0);removed_neighbors.assign(V,0);
    wd.resize(V);ws.assign(V,0);target_stamp.assign(V,0);target_limit.resize(V);
    // First make each adjacency list unique. Input symmetry is then preserved
    // by every pruning and contraction operation, including parallel edges.
    int64_t max_weight=0,small_count=0,arc_count_all=0;
    for(auto& es:adj) {
        std::sort(es.begin(),es.end(),[](const Edge&a,const Edge&b){
            return a.to<b.to || (a.to==b.to && a.w<b.w);
        });
    }
    for(int32_t u=0;u<V;++u) {
        auto& es=adj[u];size_t n=0;
        for(size_t i=0;i<es.size();++i) if(es[i].to!=u && (!n || es[n-1].to!=es[i].to)) es[n++]=es[i];
        es.resize(n);
        for(const Edge& e:es) max_weight=std::max(max_weight,e.w);
    }
    for(const auto& es:adj) for(const Edge& e:es) {
        ++arc_count_all;if(e.w<max_weight/100) ++small_count;
    }
    ReusableHeap pq;
#ifdef PROFILE
    auto pruning_start=std::chrono::steady_clock::now();
#endif
    if(small_count>arc_count_all/4) for(int32_t src=0;src<V;++src) {
        new_epoch(ws,epoch);pq.clear();wd[src]=0;ws[src]=epoch;pq.push({0,src});
        int settled=0;
        while(!pq.empty() && settled<48) {
            auto [d,u]=pq.top();pq.pop();if(d!=wd[u]) continue;++settled;
            for(const Edge& e:adj[u]) {
                const int64_t nd=d+e.w;
                if(ws[e.to]!=epoch || nd<wd[e.to]) {
                    ws[e.to]=epoch;wd[e.to]=nd;pq.push({nd,e.to});
                }
            }
        }
        auto& es=adj[src];size_t n=0;
        for(size_t i=0;i<es.size();++i) {
            const Edge e=es[i];
            if(ws[e.to]==epoch && wd[e.to]<e.w) {
                // A strictly shorter nonnegative walk cannot use this edge
                // in either direction. Removing both directions is safe.
                erase_neighbor(adj[e.to],src);pruned_arcs+=2;
            } else es[n++]=e;
        }
        es.resize(n);
    }
#ifdef PROFILE
    std::fprintf(stderr,"[profile] pruning_s=%.6f pruned_arcs=%llu\n",
        std::chrono::duration<double>(std::chrono::steady_clock::now()-pruning_start).count(),
        static_cast<unsigned long long>(pruned_arcs));
    auto contraction_start=std::chrono::steady_clock::now();
#endif
    Heap order;
    for(int32_t v=0;v<V;++v) order.push({-20*int64_t(adj[v].size()),v});
    vector<Shortcut> candidates;
    vector<unsigned char> deferred(V,0);
    int32_t next_rank=0;
    auto wake=[&](int32_t u) {
        if(deferred[u] && adj[u].size()*adj[u].size()<=20000) {
            deferred[u]=0;
            order.push({-20*int64_t(adj[u].size())+2*level[u]+removed_neighbors[u],u});
        }
    };
    // Save one complete witness result. It can be reused only if NO node was
    // contracted since it was computed: this also preserves avoidance of v.
    int32_t cached_v=-1,cached_rank=-1;
    while(!order.empty()) {
        const int32_t v=order.top().second;order.pop();
        if(rank_id[v]>=0) continue;
        const size_t d=adj[v].size();
        if(d*d>20000) {deferred[v]=1;continue;}
        if(cached_v!=v || cached_rank!=next_rank) {
            symmetric_shortcuts(v,candidates,pq);++priority_checks;
            cached_v=v;cached_rank=next_rank;
        }
        const int64_t priority=20*(int64_t(candidates.size())-int64_t(d))
                              +2*level[v]+removed_neighbors[v];
        if(!order.empty() && priority>order.top().first) {
            order.push({priority,v});++priority_requeues;continue;
        }
        rank_id[v]=next_rank++;
        up[v]=std::move(adj[v]);
        for(const Edge& e:up[v]) {
            erase_neighbor(adj[e.to],v);
            level[e.to]=std::max(level[e.to],level[v]+1);
            removed_neighbors[e.to]+=2;
        }
        for(const Shortcut& c:candidates) add_undirected_edge(c.from,c.to,c.w);
        // Reconsider dense vertices after ALL shortcuts are installed.
        for(const Edge& e:up[v]) wake(e.to);
#ifdef PROFILE
        if(next_rank%100000==0) std::fprintf(stderr,"[profile] contracted=%d/%d\n",next_rank,V);
#endif
    }
    for(int32_t v=0;v<V;++v) if(rank_id[v]<0) {rank_id[v]=V;up[v]=std::move(adj[v]);}
    vector<vector<Edge>>().swap(adj);
    vector<int64_t>().swap(wd);vector<uint32_t>().swap(ws);
    vector<int64_t>().swap(target_limit);vector<uint32_t>().swap(target_stamp);
#ifdef PROFILE
    size_t arcs=0;for(const auto& es:up) arcs+=es.size();
    std::fprintf(stderr,"[profile] contraction_s=%.6f core=%d upward_arcs=%zu witnesses=%llu capped=%llu scans=%llu priority_checks=%llu requeues=%llu new_edges=%llu\n",
        std::chrono::duration<double>(std::chrono::steady_clock::now()-contraction_start).count(),V-next_rank,arcs,
        static_cast<unsigned long long>(witness_calls),static_cast<unsigned long long>(witness_caps),
        static_cast<unsigned long long>(witness_scans),static_cast<unsigned long long>(priority_checks),
        static_cast<unsigned long long>(priority_requeues),static_cast<unsigned long long>(shortcuts_added));
#endif
}

static void prepare_graph() {
    if(!(FLAGS & FLAG_DIRECTED)) {prepare_undirected();return;}
    radj.resize(V); up.resize(V); back.resize(V);
    // Very sparse directed graphs benefit from meeting in the middle without
    // the up-front cost of a hierarchy. This choice changes only performance.
    plain_bidirectional=(FLAGS&FLAG_DIRECTED) && int64_t(E)<=4LL*V;
    if(plain_bidirectional) {
        up=std::move(adj);
        for(int32_t u=0;u<V;++u) for(const Edge&e:up[u]) back[e.to].push_back({u,e.w});
        vector<vector<Edge>>().swap(radj);
        return;
    }
    rank_id.assign(V,-1); level.assign(V,0); removed_neighbors.assign(V,0);
    wd.resize(V); ws.assign(V,0);
    target_stamp.assign(V,0); target_limit.resize(V);
    // On very broad weight distributions, discard only edges for which a
    // strictly shorter path has actually been found. This is a bounded
    // instance of the foundation Dijkstra, not a heuristic distance estimate.
    int64_t max_weight=0, small_count=0, arc_count_all=0;
    for(const auto& es:adj) for(const Edge& e:es) max_weight=std::max(max_weight,e.w);
    for(const auto& es:adj) for(const Edge& e:es) {
        ++arc_count_all; if(e.w<max_weight/100) ++small_count;
    }
    if(small_count>arc_count_all/4) for(int32_t s=0;s<V;++s) {
        new_epoch(ws,epoch); Heap pq;
        wd[s]=0; ws[s]=epoch; pq.push({0,s});
        int settled=0;
        while(!pq.empty() && settled<48) {
            auto [d,u]=pq.top(); pq.pop(); if(d!=wd[u]) continue;
            ++settled;
            for(const Edge& e:adj[u]) {
                int64_t nd=d+e.w;
                if(ws[e.to]!=epoch || nd<wd[e.to]) {
                    ws[e.to]=epoch; wd[e.to]=nd; pq.push({nd,e.to});
                }
            }
        }
        auto& es=adj[s];
        es.erase(std::remove_if(es.begin(),es.end(),[&](const Edge&e){
            return ws[e.to]==epoch && wd[e.to]<e.w;
        }),es.end());
    }
    // Collapse parallel arcs to their minimum and omit nonnegative self-loops.
    for(int32_t u=0;u<V;++u) {
        auto& es=adj[u];
        std::sort(es.begin(),es.end(),[](const Edge&a,const Edge&b){
            return a.to<b.to || (a.to==b.to && a.w<b.w);
        });
        size_t n=0;
        for(size_t i=0;i<es.size();++i) if(es[i].to!=u && (!n || es[n-1].to!=es[i].to)) es[n++]=es[i];
        es.resize(n);
        for(const Edge&e:es) radj[e.to].push_back({u,e.w});
    }
    Heap order;
    for(int32_t v=0;v<V;++v) order.push({-10*int64_t(adj[v].size()+radj[v].size()),v});
    vector<Shortcut> shortcuts;
    int32_t next_rank=0;
    while(!order.empty()) {
        int32_t v=order.top().second; order.pop();
        // Keep a residual core rather than allowing huge intermediate fills.
        // Core arcs remain uncontracted and are searched normally by Dijkstra.
        if(adj[v].size()*radj[v].size()>20000) continue;
        find_shortcuts(v,shortcuts);
        int64_t degree=int64_t(adj[v].size()+radj[v].size());
        int64_t priority=10*(int64_t(shortcuts.size())-degree)
                         +2*level[v]+removed_neighbors[v];
        if(!order.empty() && priority>order.top().first) {
            order.push({priority,v}); continue;
        }
        rank_id[v]=next_rank++;
        up[v]=std::move(adj[v]); back[v]=std::move(radj[v]);
        for(const Edge&e:up[v]) {
            auto& es=radj[e.to];
            es.erase(std::remove_if(es.begin(),es.end(),[v](const Edge&a){return a.to==v;}),es.end());
            level[e.to]=std::max(level[e.to],level[v]+1); ++removed_neighbors[e.to];
        }
        for(const Edge&e:back[v]) {
            auto& es=adj[e.to];
            es.erase(std::remove_if(es.begin(),es.end(),[v](const Edge&a){return a.to==v;}),es.end());
            level[e.to]=std::max(level[e.to],level[v]+1); ++removed_neighbors[e.to];
        }
        for(const Shortcut&a:shortcuts) add_arc(a.from,a.to,a.w);
    }
    for(int32_t v=0;v<V;++v) if(rank_id[v]<0) {
        rank_id[v]=V; up[v]=std::move(adj[v]); back[v]=std::move(radj[v]);
    }
    vector<vector<Edge>>().swap(adj); vector<vector<Edge>>().swap(radj);
    vector<int64_t>().swap(wd); vector<uint32_t>().swap(ws);
#ifdef PROFILE
    size_t arc_count=0; for(const auto& a:up) arc_count+=a.size();
    std::fprintf(stderr,"contracted=%d core=%d arcs=%zu\n",next_rank,V-next_rank,arc_count);
#endif
}

// Foundation Dijkstra extended to the forward and reverse upward graphs.
// Timestamped distances replace the O(V) clear before every query.
// Each frontier stops at best (not at the sum of its minimum and the other
// frontier's minimum, which is not a valid stopping rule for CH queries).
static int64_t dijkstra(int32_t s,int32_t t) {
    if(s==t) return 0;
    static vector<int64_t> dist[2];
    static vector<uint32_t> seen[2];
    static uint32_t generation=0;
    if(dist[0].empty()) for(int k=0;k<2;++k) {dist[k].resize(V);seen[k].assign(V,0);}
    if(++generation==0) {for(auto& a:seen) std::fill(a.begin(),a.end(),0); generation=1;}
    static ReusableHeap pq[2];
    pq[0].clear();pq[1].clear();
    dist[0][s]=dist[1][t]=0;
    seen[0][s]=seen[1][t]=generation;
    pq[0].push({0,s}); pq[1].push({0,t});
    int64_t best=INF;
    while(!pq[0].empty() || !pq[1].empty()) {
        if(plain_bidirectional && (pq[0].empty() || pq[1].empty() ||
           pq[0].top().first+pq[1].top().first>=best)) break;
        for(int k=0;k<2;++k) if(!pq[k].empty() && pq[k].top().first>=best) pq[k].clear();
        if(pq[0].empty() && pq[1].empty()) break;
        int k=pq[0].empty()?1:pq[1].empty()?0:(pq[1].top().first<pq[0].top().first);
        if(plain_bidirectional) k=pq[1].size()<pq[0].size();
        auto [d,u]=pq[k].top(); pq[k].pop();
        if(d!=dist[k][u]) continue;
        if(seen[1-k][u]==generation) best=std::min(best,d+dist[1-k][u]);
        const auto& incoming=symmetric_hierarchy?up[u]:(k?up[u]:back[u]);
        bool stalled=false;
        for(const Edge&e:incoming) if(seen[k][e.to]==generation && dist[k][e.to]+e.w<d) {stalled=true;break;}
        if(stalled) continue;
        const auto& outgoing=symmetric_hierarchy?up[u]:(k?back[u]:up[u]);
        for(const Edge&e:outgoing) {
            int64_t nd=d+e.w;
            if(nd>=best) continue;
            if(seen[k][e.to]!=generation || nd<dist[k][e.to]) {
                seen[k][e.to]=generation; dist[k][e.to]=nd; pq[k].push({nd,e.to});
                if(seen[1-k][e.to]==generation) best=std::min(best,nd+dist[1-k][e.to]);
            }
        }
    }
    return best==INF?-1:best;
}


// V3: cache upward Dijkstra distances when many queries amortize the work.
// Every label is computed from this invocation's graph. Intersecting the two
// upward searches is the same exact meeting criterion as the CH query above.
static vector<vector<Edge>> query_labels[2];
static bool build_query_labels(int32_t queries) {
    if(plain_bidirectional || V>150000 || int64_t(queries)<4LL*V) return false;
    for(int32_t u=0;u<V;++u) if(rank_id[u]>=V) return false;
    const size_t entry_cap=24000000,scan_cap=200000000;
    size_t entries=0,scans=0;
    vector<int64_t> distance(V);
    vector<uint32_t> stamp(V,0);
    uint32_t generation=0;
    vector<int32_t> descending(V),touched;
    for(int32_t u=0;u<V;++u) descending[rank_id[u]]=u;
    for(int side=0;side<(symmetric_hierarchy?1:2);++side) {
        query_labels[side].resize(V);
        const auto& graph=side?back:up;
        for(int32_t rank=V-1;rank>=0;--rank) {
            const int32_t source=descending[rank];
            ++generation;touched.clear();distance[source]=0;stamp[source]=generation;
            touched.push_back(source);
            for(const Edge& edge:graph[source]) {
                for(const Edge& entry:query_labels[side][edge.to]) {
                    if(++scans>scan_cap) goto fallback;
                    const int64_t nd=edge.w+entry.w;
                    if(stamp[entry.to]!=generation) {
                        stamp[entry.to]=generation;distance[entry.to]=nd;
                        touched.push_back(entry.to);
                    } else distance[entry.to]=std::min(distance[entry.to],nd);
                }
            }
            entries+=touched.size();
            if(entries>entry_cap) goto fallback;
            std::sort(touched.begin(),touched.end());
            auto& label=query_labels[side][source];label.reserve(touched.size());
            for(int32_t u:touched) label.push_back({u,distance[u]});
        }
    }
#ifdef PROFILE
    std::fprintf(stderr,"[profile] labels entries=%zu scans=%zu\n",entries,scans);
#endif
    return true;
fallback:
    for(auto& labels:query_labels) vector<vector<Edge>>().swap(labels);
#ifdef PROFILE
    std::fprintf(stderr,"[profile] labels budget reached; using CH queries\n");
#endif
    return false;
}
static int64_t label_query(int32_t s,int32_t t) {
    const auto& a=query_labels[0][s];
    const auto& b=query_labels[symmetric_hierarchy?0:1][t];
    size_t i=0,j=0;int64_t best=INF;
    while(i<a.size() && j<b.size()) {
        if(a[i].to<b[j].to) ++i;
        else if(a[i].to>b[j].to) ++j;
        else {best=std::min(best,a[i].w+b[j].w);++i;++j;}
    }
    return best==INF?-1:best;
}

static void run_queries(const char* qpath, const char* opath) {
    std::FILE* qf = std::fopen(qpath, "r");
    if (!qf) { std::fprintf(stderr, "cannot open query file: %s\n", qpath); std::exit(1); }
    std::FILE* of = std::fopen(opath, "w");
    if (!of) { std::fprintf(stderr, "cannot open output file: %s\n", opath); std::exit(1); }

    GraphInput input(qf);
    int32_t Q;
    if (!input.integer(Q)) {
        std::fprintf(stderr, "bad query header\n"); std::exit(1);
    }
    const bool labeled=build_query_labels(Q);
    char output_buffer[1<<16];
    std::setvbuf(of,output_buffer,_IOFBF,sizeof(output_buffer));
    for (int32_t i = 0; i < Q; ++i) {
        int32_t s, t;
        if (!input.integer(s) || !input.integer(t)) {
            std::fprintf(stderr, "bad query %d\n", i); std::exit(1);
        }
        int64_t d = labeled?label_query(s,t):dijkstra(s, t);
        std::fprintf(of, "%lld\n", (long long)d);
    }
    std::fclose(qf);
    std::fclose(of);
}

int main(int argc, char** argv) {
    if (argc != 4) {
        std::fprintf(stderr, "usage: %s <graph_file> <query_file> <output_file>\n", argv[0]);
        return 1;
    }
#ifdef PROFILE
    auto reading=std::chrono::steady_clock::now();
#endif
    read_graph(argv[1]);
#ifdef PROFILE
    std::fprintf(stderr,"[profile] read_s=%.6f\n",std::chrono::duration<double>(std::chrono::steady_clock::now()-reading).count());
    auto phase=std::chrono::steady_clock::now();
#endif
    prepare_graph();
#ifdef PROFILE
    std::fprintf(stderr,"preprocess %.3f s\n",std::chrono::duration<double>(std::chrono::steady_clock::now()-phase).count());
#endif
#ifdef PROFILE
    auto queries_start=std::chrono::steady_clock::now();
#endif
    run_queries(argv[2], argv[3]);
#ifdef PROFILE
    std::fprintf(stderr,"[profile] queries_s=%.6f\n",std::chrono::duration<double>(std::chrono::steady_clock::now()-queries_start).count());
#endif
    return 0;
}
