/* f(n) for MO 454425: fewest edges shared by two triangulations of an n-point set.
 *
 * For a general-position set P with h hull points, two triangulations share at least
 *   f(P) = 6n - 6 - 2h - C(n,2) + oct(P)
 * edges (hull edges are shared; interior edges of two triangulations form a thickness-two set, and every
 * thickness-two set of interior segments extends to two triangulations), and this is attained.
 * For each order type we compute f(P) exactly when f(P) <= F, else record F+1.
 * usage: fmin file.b08|file.b16|file.b32 n F [limit] [maxshow]   (.b32: unsigned LE, < 2^30 so orient fits int64)     build: cc -O2 -o fmin fmin.c
 * F = -1 prints only the hull size of each set, one per line (to check against the database's extremNN files).
 * Search core (odd_cycle, packing, oct_le) is copied from oct2.c.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 set_t;  /* segment sets (ns <= 128) */
static int ctz(set_t v) {
    uint64_t lo = (uint64_t)v;
    return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(v >> 64));
}
#define BIT(i) ((set_t)1 << (i))

#define MAXP 16
#define MAXS (MAXP * (MAXP - 1) / 2)

static int n, ns, usepack;
static int64_t X[MAXP], Y[MAXP];
static int sa[MAXS], sb[MAXS];
static set_t adj[MAXS];  /* crossing graph as bitsets */

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
static int odd_cycle(set_t alive, int *cyc) {
    int col[MAXS], par[MAXS], dep[MAXS], queue[MAXS];
    for (int i = 0; i < ns; i++) col[i] = -1;
    for (int r = 0; r < ns; r++) {
        if (!((alive >> r) & 1) || col[r] >= 0) continue;
        int h = 0, t = 0;
        queue[t++] = r; col[r] = 0; par[r] = -1; dep[r] = 0;
        while (h < t) {
            int u = queue[h++];
            set_t nb = adj[u] & alive;
            while (nb) {
                int v = ctz(nb); nb &= nb - 1;
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
static int packing(set_t alive, int cap) {
    int cyc[MAXS], cnt = 0, len;
    while (cnt < cap && (len = odd_cycle(alive, cyc)) > 0) {
        for (int i = 0; i < len; i++) alive &= ~BIT(cyc[i]);
        cnt++;
    }
    return cnt;
}

/* can we delete <= k vertices to make the alive graph bipartite? */
static int oct_le(set_t alive, int k) {
    int cyc[MAXS];
    int len = odd_cycle(alive, cyc);
    if (len == 0) return 1;
    if (k == 0) return 0;
    if (usepack && packing(alive, k + 1) > k) return 0;
    for (int i = 0; i < len; i++)
        if (oct_le(alive & ~BIT(cyc[i]), k - 1)) return 1;
    return 0;
}

static int hull_size(void) {
    int h = 0;
    for (int i = 0; i < n; i++) {
        int on = 0;
        for (int j = 0; j < n && !on; j++) {
            if (j == i) continue;
            int pos = 0, neg = 0;
            for (int k = 0; k < n; k++) {
                if (k == i || k == j) continue;
                if (orient(i, j, k) > 0) pos++; else neg++;
            }
            if (pos == 0 || neg == 0) on = 1;
        }
        h += on;
    }
    return h;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: fmin file.b16 n F [limit]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("open"); return 1; }
    n = atoi(argv[2]);
    int F = atoi(argv[3]);
    long long limit = argc > 4 ? atoll(argv[4]) : -1;
    int maxshow = argc > 5 ? atoi(argv[5]) : 2;
    usepack = 1;
    ns = n * (n - 1) / 2;
    if (ns > 128) { fprintf(stderr, "n too large for 128-bit sets\n"); return 1; }
    for (int i = 0, s = 0; i < n; i++) for (int j = i + 1; j < n; j++, s++) { sa[s] = i; sb[s] = j; }
    static long long hist[MAXP + 1][64];
    long long total = 0;
    int shown[MAXP + 1][64] = {{0}};
    int w = strstr(argv[1], ".b08") ? 1 : strstr(argv[1], ".b32") ? 4 : 2;  /* bytes per coordinate */
    unsigned char buf[8 * MAXP];
    while ((limit < 0 || total < limit) && fread(buf, 2 * w, n, f) == (size_t)n) {
        for (int i = 0; i < n; i++) {
            if (w == 1) { X[i] = buf[2 * i]; Y[i] = buf[2 * i + 1]; }
            else if (w == 4) {
                unsigned char *q = buf + 8 * i;
                X[i] = (int64_t)q[0] | (int64_t)q[1] << 8 | (int64_t)q[2] << 16 | (int64_t)q[3] << 24;
                Y[i] = (int64_t)q[4] | (int64_t)q[5] << 8 | (int64_t)q[6] << 16 | (int64_t)q[7] << 24;
            } else { X[i] = buf[4 * i] | (buf[4 * i + 1] << 8); Y[i] = buf[4 * i + 2] | (buf[4 * i + 3] << 8); }
        }
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) for (int c = b + 1; c < n; c++)
            if (orient(a, b, c) == 0) { fprintf(stderr, "collinear triple in set %lld\n", total); return 2; }
        int h = hull_size();
        if (F < 0) { printf("%d\n", h); total++; continue; }
        int base = 6 * n - 6 - 2 * h - ns;
        int fval = F + 1;
        if (h <= F && F - base >= 0) {
            for (int s = 0; s < ns; s++) adj[s] = 0;
            for (int s = 0; s < ns; s++) for (int t = s + 1; t < ns; t++)
                if (cross(s, t)) { adj[s] |= BIT(t); adj[t] |= BIT(s); }
            set_t all = (ns == 128) ? ~(set_t)0 : (BIT(ns) - 1);
            for (int k = 0; k <= F - base; k++)
                if (oct_le(all, k)) { fval = base + k; break; }
        }
        hist[h][fval]++;
        if (fval <= F && shown[h][fval] < maxshow) {
            shown[h][fval]++;
            printf("set %lld h=%d f=%d :", total, h, fval);
            for (int i = 0; i < n; i++) printf(" (%lld,%lld)", (long long)X[i], (long long)Y[i]);
            printf("\n");
        }
        total++;
    }
    if (F < 0) return 0;
    printf("n=%d sets=%lld F=%d  counts by hull size h, f (f=%d means > %d):\n", n, total, F, F + 1, F);
    for (int h = 3; h <= n; h++) {
        long long row = 0;
        for (int v = 0; v <= F + 1; v++) row += hist[h][v];
        if (!row) continue;
        printf("  h=%d:", h);
        for (int v = 0; v <= F + 1; v++) if (hist[h][v]) printf(" f%d:%lld", v, hist[h][v]);
        printf("\n");
    }
    return 0;
}
