// q/304266: every rooted binary tree on n nodes (<= 2 children, unordered) has a bijective labelling by 0..n-1,
// root 0, child = parent + 2^k?  Enumerates all trees of size n, skips those covered by the known reductions
// (root split a == b, or a or b of the form 2^k - 1: compose smaller labellings), backtracks the rest.
// Adds the imbalance-one and unary-prefix reductions proved in PROGRESS_304266.md.
// Reductions are disabled if earlier sizes are unverified.
// usage: label nmin nmax [budget] [noreduce] [kmin]   prints per n: trees, reduced-away, searched, max/avg search nodes, FAILS
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
static int kmin = 0, noreduce = 0;
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

static bool pow2m1(int s) { return s > 0 && ((s + 1) & s) == 0; }
static bool pow2(int s) { return s > 0 && (s & (s-1)) == 0; }
// Unary-prefix proposition in PROGRESS_304266.md.
static bool prefix_reduce(int id, int b) {
    for (int d=1; pool[id].l>=0 && pool[id].r<0; ++d) {
        id=pool[id].l;
        int c=pool[id].size;
        if ((c==b || c==b+1) && pow2(d+2)) return true;
        if ((b==c || b==c+1) && pow2(d+1)) return true;
    }
    return false;
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 6) return 2;
    int nmin = atoi(argv[1]), nmax = atoi(argv[2]);
    if (nmin < 1 || nmax < nmin || nmax > 25) return 2;
    bool inductive_ok = (nmin == 1), any_fail = false, any_unknown = false;
    budget = argc > 3 ? atoll(argv[3]) : 100000000LL;
    noreduce = argc > 4 ? atoi(argv[4]) : 0;               // 1: search every tree, no reductions
    kmin = argc > 5 ? atoi(argv[5]) : 0;                   // mutant: forbid steps 2^k, k < kmin
    if (budget < 1 || kmin < 0 || kmin > 30) return 2;
    if (kmin > 0) noreduce = 1; // the reduction proofs use unit steps
    build(nmax);
    for (n = nmin; n <= nmax; n++) {
        long long reduced = 0, searched = 0, maxn = 0, sumn = 0, fails = 0, unknown = 0;
        for (int id : bysize[n]) {
            const T &t = pool[id];
            if (noreduce || !inductive_ok) {} else if (t.l >= 0 && t.r >= 0) {
                int a = pool[t.l].size, b = pool[t.r].size;
                if (a - b <= 1 || pow2m1(a) || pow2m1(b) || prefix_reduce(t.l,b) || prefix_reduce(t.r,a)) { reduced++; continue; }
            } else if (t.l >= 0) { reduced++; continue; }   // single child: label it 1, shift child's tree by 1
            else { reduced++; continue; }                   // n = 1
            cnt = 0; order.clear(); flatten(id, -1);
            used = 1; lab[0] = 0; nodes = 0;
            int r = n == 1 ? 1 : rec(1);
            if (r == 1) {                                   // independent check of the labelling
                uint64_t seen = 0;
                for (int v = 0; v < n; v++) {
                    if (lab[v] < 0 || lab[v] >= n || (seen >> lab[v] & 1)) { printf("BAD labelling\n"); return 1; }
                    seen |= 1ULL << lab[v];
                    if (v) { int d = lab[v] - lab[par[v]]; if (d <= 0 || (d & (d - 1))) { printf("BAD edge\n"); return 1; } }
                }
                if (lab[0] != 0) { printf("BAD root\n"); return 1; }
            }
            searched++; maxn = max(maxn, nodes); sumn += nodes;
            if (r == 0) { any_fail = true; fails++; printf("COUNTEREXAMPLE n=%d tree id %d\n", n, id); }
            if (r < 0) { any_unknown = true; unknown++; printf("budget exhausted n=%d tree id %d\n", n, id); }
        }
        printf("n=%2d trees=%zu reduced=%lld searched=%lld max_nodes=%lld avg_nodes=%.1f fails=%lld unknown=%lld\n",
               n, bysize[n].size(), reduced, searched, maxn, searched ? (double)sumn / searched : 0.0, fails, unknown);
        fflush(stdout);
        if (fails || unknown) inductive_ok = false;
    }
    return any_fail ? 1 : (any_unknown ? 2 : 0);
}
