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
        Heap pq;
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

static void prepare_graph() {
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
    Heap pq[2];
    dist[0][s]=dist[1][t]=0;
    seen[0][s]=seen[1][t]=generation;
    pq[0].push({0,s}); pq[1].push({0,t});
    int64_t best=INF;
    while(!pq[0].empty() || !pq[1].empty()) {
        if(plain_bidirectional && (pq[0].empty() || pq[1].empty() ||
           pq[0].top().first+pq[1].top().first>=best)) break;
        for(int k=0;k<2;++k) if(!pq[k].empty() && pq[k].top().first>=best) pq[k]=Heap();
        if(pq[0].empty() && pq[1].empty()) break;
        int k=pq[0].empty()?1:pq[1].empty()?0:(pq[1].top().first<pq[0].top().first);
        if(plain_bidirectional) k=pq[1].size()<pq[0].size();
        auto [d,u]=pq[k].top(); pq[k].pop();
        if(d!=dist[k][u]) continue;
        if(seen[1-k][u]==generation) best=std::min(best,d+dist[1-k][u]);
        const auto& incoming=k?up[u]:back[u];
        bool stalled=false;
        for(const Edge&e:incoming) if(seen[k][e.to]==generation && dist[k][e.to]+e.w<d) {stalled=true;break;}
        if(stalled) continue;
        const auto& outgoing=k?back[u]:up[u];
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

static void run_queries(const char* qpath, const char* opath) {
    std::FILE* qf = std::fopen(qpath, "r");
    if (!qf) { std::fprintf(stderr, "cannot open query file: %s\n", qpath); std::exit(1); }
    std::FILE* of = std::fopen(opath, "w");
    if (!of) { std::fprintf(stderr, "cannot open output file: %s\n", opath); std::exit(1); }

    int32_t Q;
    if (std::fscanf(qf, "%d", &Q) != 1) {
        std::fprintf(stderr, "bad query header\n"); std::exit(1);
    }
    for (int32_t i = 0; i < Q; ++i) {
        int32_t s, t;
        if (std::fscanf(qf, "%d %d", &s, &t) != 2) {
            std::fprintf(stderr, "bad query %d\n", i); std::exit(1);
        }
        int64_t d = dijkstra(s, t);
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
    read_graph(argv[1]);
#ifdef PROFILE
    auto phase=std::chrono::steady_clock::now();
#endif
    prepare_graph();
#ifdef PROFILE
    std::fprintf(stderr,"preprocess %.3f s\n",std::chrono::duration<double>(std::chrono::steady_clock::now()-phase).count());
#endif
    run_queries(argv[2], argv[3]);
    return 0;
}
