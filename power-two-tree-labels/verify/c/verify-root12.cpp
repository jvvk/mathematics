// Exact exhaustive check for MO q/304266, with the stronger condition that
// every branching root has children labelled 1 and 2.
// Enumerates unordered rooted trees with at most two children per vertex.
// All trees are directly searched; no inductive reductions are used.
// Build: clang++ -O3 -std=c++17 verify-root12.cpp -o verify-root12
// Run: ./verify-root12 NMAX [PER_TREE_NODE_BUDGET]
// Exit 0: all trees checked successfully; 1: strong-condition failure;
//      2: budget exhaustion or invalid arguments.
// WARNING: tree enumeration grows exponentially; NMAX is limited to 25.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <algorithm>
using namespace std;

struct T { int size, l, r; };               // l, r: indices into pool (-1 = none); canonical: l >= r
vector<T> pool;
vector<vector<int>> bysize;                  // tree ids of each size

static void build(int nmax) {
    bysize.assign(nmax + 1, {});
    pool.push_back({1, -1, -1}); bysize[1].push_back(0);
    for (int n = 2; n <= nmax; n++) {
        for (int c : bysize[n - 1]) { pool.push_back({n, c, -1}); bysize[n].push_back((int)pool.size() - 1); }
        for (int a = 1; a <= n - 2; a++) {
            int b = n - 1 - a; if (a < b) continue;
            for (int x : bysize[a]) for (int y : bysize[b]) {
                if (a == b && x < y) continue;
                pool.push_back({n, x, y}); bysize[n].push_back((int)pool.size() - 1);
            }
        }
    }
}

static int n, par[64], lab[64], sz[64], cnt;
static long long budget, nodes;
static uint64_t used;
static constexpr int kmin = 0;
static vector<int> order;

static void flatten(int id, int p) {                 // preorder, larger child first
    int v = cnt++; par[v] = p; order.push_back(v);
    const T &t = pool[id]; sz[v] = t.size;
    if (t.l >= 0) flatten(t.l, v);
    if (t.r >= 0) flatten(t.r, v);
}

static int rec(int i) {                              // 1 found, 0 impossible, -1 budget exhausted
    if (i == n) return 1;
    if (++nodes > budget) return -1;
    int v = order[i], x = lab[par[v]];
    if (par[v] == 0) return rec(i + 1);
    for (int k = kmin; (1 << k) + x < n; k++) {
        int y = x + (1 << k);
        if (y > n - sz[v] || (used >> y & 1)) continue;
        used |= 1ULL << y; lab[v] = y;
        int r = rec(i + 1);
        used &= ~(1ULL << y);
        if (r != 0) return r;
    }
    return 0;
}

static void show(int id) { printf("("); if (pool[id].l>=0) show(pool[id].l); if(pool[id].r>=0) show(pool[id].r); printf(")"); }


int main(int argc, char **argv) {
    if (argc < 2 || argc > 3) { fprintf(stderr,"Usage: %s NMAX [PER_TREE_NODE_BUDGET]\n",argv[0]); return 2; }
    int nmin = 1, nmax = atoi(argv[1]);
    if (nmax < 1 || nmax > 25) return 2;
    budget = argc > 2 ? atoll(argv[2]) : 10000000LL;
    if (budget < 1) return 2;
    bool any_fail = false, any_unknown = false;
    build(nmax);
    for (n = nmin; n <= nmax; n++) {
        long long reduced = 0, searched = 0, maxn = 0, sumn = 0, fails = 0, unknown = 0;
        for (int id : bysize[n]) {
            const T &t = pool[id];
            fill(lab,lab+64,-1);
            cnt = 0; order.clear(); flatten(id, -1);
            used = 1; lab[0] = 0; nodes = 0;
            int left = n>1 ? 1 : -1, right = t.r>=0 ? 1 + pool[t.l].size : -1;
            if (left>=0) { lab[left]=1; used|=2; }
            if (right>=0) { lab[right]=2; used|=4; }
            int r = n == 1 ? 1 : rec(1);
            if (r==0 && right>=0) { fill(lab,lab+64,-1); lab[0]=0; lab[left]=2; lab[right]=1; used=7; r=rec(1); }
            if (r == 1) {                                   // independent check of the labelling
                uint64_t seen = 0;
                for (int v = 0; v < n; v++) {
                    if (lab[v] < 0 || lab[v] >= n || (seen >> lab[v] & 1)) { printf("BAD labelling\n"); return 1; }
                    seen |= 1ULL << lab[v];
                    if (v) { int d = lab[v] - lab[par[v]]; if (d <= 0 || (d & (d - 1))) { printf("BAD edge\n"); return 1; } }
                }
                if (right>=0 && !((lab[left]==1 && lab[right]==2) || (lab[left]==2 && lab[right]==1))) { printf("BAD root children\n"); return 1; }
                if (lab[0] != 0) { printf("BAD root\n"); return 1; }
            }
            searched++; maxn = max(maxn, nodes); sumn += nodes;
            if (r == 0) { any_fail = true; fails++; printf("ROOT12 FAILURE n=%d tree id %d ", n, id); show(id); printf("\n"); }
            if (r < 0) { any_unknown = true; unknown++; printf("budget exhausted n=%d tree id %d\n", n, id); }
        }
        printf("n=%2d trees=%zu reduced=%lld searched=%lld max_nodes=%lld avg_nodes=%.1f fails=%lld unknown=%lld\n",
               n, bysize[n].size(), reduced, searched, maxn, searched ? (double)sumn / searched : 0.0, fails, unknown);
        fflush(stdout);
    }
    return any_fail ? 1 : (any_unknown ? 2 : 0);
}
