/* Base chains: for each m in [lo, hi], a parity-aligned triangular chain on [1..m] from 1 to b(m),
   b = 2 (m even), 9 (m odd); adjacent sums are odd triangular numbers. Posa rotation-extension,
   start fixed at 1. Output: one line per m: "m v1 v2 ... vm". Single-threaded. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int is_odd_tri(long s) {
    if (s % 2 == 0) return 0;
    long d = 8 * s + 1, r = 0;
    while ((r + 1) * (r + 1) <= d) r++;           /* fine: only used to build the triangular list */
    return r * r == d;
}

static unsigned long long rng = 88172645463325252ULL;
static unsigned long long xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

int main(int argc, char **argv) {
    int lo = atoi(argv[1]), hi = atoi(argv[2]);
    int maxm = hi;
    /* odd triangular numbers up to 2*maxm */
    int *ot = malloc(sizeof(int) * (maxm + 10)); int not_ = 0;
    for (long k = 1; k * (k + 1) / 2 <= 2L * maxm; k++) { long t = k * (k + 1) / 2; if (t % 2) ot[not_++] = (int)t; }
    (void)is_odd_tri;
    int *adjstart = malloc(sizeof(int) * (maxm + 2)), *adj = malloc(sizeof(int) * (size_t)maxm * 64);
    int *path = malloc(sizeof(int) * (maxm + 1)), *pos = malloc(sizeof(int) * (maxm + 1));
    int *cand = malloc(sizeof(int) * 128);
    int nfail = 0;
    for (int m = lo; m <= hi; m++) {
        int b = (m % 2 == 0) ? 2 : 9;
        rng = 88172645463325252ULL ^ (unsigned long long)m * 0x9E3779B97F4A7C15ULL;
        int e = 0;
        for (int v = 1; v <= m; v++) {
            adjstart[v] = e;
            for (int i = 0; i < not_; i++) { int w = ot[i] - v; if (w > m) break; if (w >= 1 && w != v) adj[e++] = w; }
        }
        adjstart[m + 1] = e;
        int ok = 0;
        for (int attempt = 0; attempt < 200 && !ok; attempt++) {
            for (int v = 1; v <= m; v++) pos[v] = -1;
            int len = 1; path[0] = 1; pos[1] = 0;
            long steps = 0, maxsteps = 200L * m + 100000;
            while (steps++ < maxsteps) {
                int v = path[len - 1];
                if (len == m && v == b) { ok = 1; break; }
                int nc = 0;
                for (int k = adjstart[v]; k < adjstart[v + 1]; k++) {
                    int w = adj[k];
                    if (pos[w] < 0 && (w != b || len == m - 1)) cand[nc++] = w;
                }
                if (nc) { int w = cand[xr() % nc]; pos[w] = len; path[len++] = w; continue; }
                nc = 0;
                for (int k = adjstart[v]; k < adjstart[v + 1]; k++) {
                    int w = adj[k];
                    if (pos[w] >= 0 && pos[w] < len - 2) cand[nc++] = w;
                }
                if (!nc) break;
                int w = cand[xr() % nc], i = pos[w];
                for (int a = i + 1, z = len - 1; a < z; a++, z--) { int t = path[a]; path[a] = path[z]; path[z] = t; }
                for (int a = i + 1; a < len; a++) pos[path[a]] = a;
            }
        }
        if (!ok) { fprintf(stderr, "FAIL %d\n", m); printf("%d FAIL\n", m); nfail++; continue; }
        printf("%d", m);
        for (int i = 0; i < m; i++) printf(" %d", path[i]);
        printf("\n");
    }
    return nfail ? 1 : 0;
}
