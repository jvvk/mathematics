/* Geometric thickness two with many edges, via order types.
 *
 * For a point set P (general position) the complete straight-line drawing K(P) has segments = all pairs.
 * A subgraph G of K_n drawn on P splits into two plane layers iff the crossing graph of its segments is
 * bipartite. So the largest geometric-thickness-two graph on P has C(n,2) - oct(P) edges, where oct(P) is the
 * minimum odd cycle transversal of the crossing graph X(P) of all C(n,2) segments.
 * 6n-18 edges on n points  <=>  oct(P) <= C(n,2) - (6n-18) for some order type P.
 *   n=9: C=36, 6n-18=36 -> need oct 0 (K_9 has geometric thickness 3: expect none);  6n-19 -> oct 1 (DGM: expect some)
 *   n=10: C=45, 6n-18=42 -> need oct <= 3.
 *
 * oct2: oct.c plus a vertex-disjoint odd-cycle packing lower bound (usepack=1, default) for speed.
 * usage: oct2 file.b16 n kmax [limit] [usepack]
 * build: cc -O2 -o oct2 oct2.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXP 12
#define MAXS (MAXP * (MAXP - 1) / 2)

static int n, ns, usepack;
static int64_t X[MAXP], Y[MAXP];
static int sa[MAXS], sb[MAXS];
static uint64_t adj[MAXS];  /* crossing graph as bitsets (ns <= 64) */

static int64_t orient(int a, int b, int c) {
    return (X[b] - X[a]) * (Y[c] - Y[a]) - (Y[b] - Y[a]) * (X[c] - X[a]);
}
static int sgn(int64_t v) { return (v > 0) - (v < 0); }
static int cross(int s, int t) {
    int a = sa[s], b = sb[s], c = sa[t], d = sb[t];
    if (a == c || a == d || b == c || b == d) return 0;
    return sgn(orient(a, b, c)) * sgn(orient(a, b, d)) < 0 && sgn(orient(c, d, a)) * sgn(orient(c, d, b)) < 0;
}

/* find an odd cycle in the graph induced by 'alive'; return its length (0 if bipartite) into cyc[] */
static int odd_cycle(uint64_t alive, int *cyc) {
    int col[MAXS], par[MAXS], dep[MAXS], queue[MAXS];
    for (int i = 0; i < ns; i++) col[i] = -1;
    for (int r = 0; r < ns; r++) {
        if (!((alive >> r) & 1) || col[r] >= 0) continue;
        int h = 0, t = 0;
        queue[t++] = r; col[r] = 0; par[r] = -1; dep[r] = 0;
        while (h < t) {
            int u = queue[h++];
            uint64_t nb = adj[u] & alive;
            while (nb) {
                int v = __builtin_ctzll(nb); nb &= nb - 1;
                if (col[v] < 0) { col[v] = col[u] ^ 1; par[v] = u; dep[v] = dep[u] + 1; queue[t++] = v; }
                else if (col[v] == col[u]) {
                    /* cycle: u..lca..v plus edge (u,v) */
                    int left[MAXS], right[MAXS], nl = 0, nr = 0, x = u, y = v;
                    while (dep[x] > dep[y]) { left[nl++] = x; x = par[x]; }
                    while (dep[y] > dep[x]) { right[nr++] = y; y = par[y]; }
                    while (x != y) { left[nl++] = x; x = par[x]; right[nr++] = y; y = par[y]; }
                    int len = 0;
                    for (int i = 0; i < nl; i++) cyc[len++] = left[i];
                    cyc[len++] = x;
                    for (int i = nr - 1; i >= 0; i--) cyc[len++] = right[i];
                    return len;
                }
            }
        }
    }
    return 0;
}

/* lower bound: greedily pack vertex-disjoint odd cycles (each needs its own deleted vertex) */
static int packing(uint64_t alive, int cap) {
    int cyc[MAXS], cnt = 0, len;
    while (cnt < cap && (len = odd_cycle(alive, cyc)) > 0) {
        for (int i = 0; i < len; i++) alive &= ~(1ULL << cyc[i]);
        cnt++;
    }
    return cnt;
}

/* can we delete <= k vertices to make the alive graph bipartite? */
static int oct_le(uint64_t alive, int k) {
    int cyc[MAXS];
    int len = odd_cycle(alive, cyc);
    if (len == 0) return 1;
    if (k == 0) return 0;
    if (usepack && packing(alive, k + 1) > k) return 0;
    for (int i = 0; i < len; i++)
        if (oct_le(alive & ~(1ULL << cyc[i]), k - 1)) return 1;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: oct file.b16 n kmax [limit]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("open"); return 1; }
    n = atoi(argv[2]);
    int kmax = atoi(argv[3]);
    long long limit = argc > 4 ? atoll(argv[4]) : -1;
    usepack = argc > 5 ? atoi(argv[5]) : 1;
    ns = n * (n - 1) / 2;
    if (ns > 64) { fprintf(stderr, "n too large for 64-bit sets\n"); return 1; }
    for (int i = 0, s = 0; i < n; i++) for (int j = i + 1; j < n; j++, s++) { sa[s] = i; sb[s] = j; }
    long long hist[64] = {0}, total = 0, shown = 0;
    int best = 1 << 30;
    unsigned char buf[4 * MAXP];
    while ((limit < 0 || total < limit) && fread(buf, 4, n, f) == (size_t)n) {
        for (int i = 0; i < n; i++) {
            X[i] = buf[4 * i] | (buf[4 * i + 1] << 8);
            Y[i] = buf[4 * i + 2] | (buf[4 * i + 3] << 8);
        }
        /* sanity: general position */
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) for (int c = b + 1; c < n; c++)
            if (orient(a, b, c) == 0) { fprintf(stderr, "collinear triple in set %lld\n", total); return 2; }
        for (int s = 0; s < ns; s++) adj[s] = 0;
        for (int s = 0; s < ns; s++) for (int t = s + 1; t < ns; t++)
            if (cross(s, t)) { adj[s] |= 1ULL << t; adj[t] |= 1ULL << s; }
        uint64_t all = (ns == 64) ? ~0ULL : ((1ULL << ns) - 1);
        int k = 0;
        while (k <= kmax && !oct_le(all, k)) k++;
        hist[k]++;
        if (k < best) { best = k; shown = 0; }
        if (k == best && k <= kmax && shown < 3) {
            shown++;
            printf("set %lld oct=%d :", total, k);
            for (int i = 0; i < n; i++) printf(" (%lld,%lld)", (long long)X[i], (long long)Y[i]);
            printf("\n");
        }
        total++;
    }
    printf("n=%d sets=%lld  histogram of min(oct, %d):", n, total, kmax + 1);
    for (int k = 0; k <= kmax + 1; k++) printf(" %d:%lld", k, hist[k]);
    printf("\n  max thickness-2 edges = C(n,2) - oct; 6n-18 = %d needs oct <= %d\n", 6 * n - 18, ns - (6 * n - 18));
    return 0;
}
