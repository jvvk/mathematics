/* Base chains for generalized pentagonal sums k(3k-1)/2, k in Z: for each m in [lo, hi], a parity-aligned chain on
   [1..m] from A0 to b(m), b = B0 (m even), B1 (m odd), whose adjacent sums are odd generalized pentagonal numbers.
   Posa rotation-extension, start fixed at A0. Usage: base_gen lo hi B0 B1 A0; the paper's data is
   base_gen 60 2965 2 19 3. Output: one line per m: "m v1 v2 ... vm". Exits 1 if some m is not found. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned long long rng = 88172645463325252ULL;
static unsigned long long xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

int main(int argc, char **argv) {
    int lo = atoi(argv[1]), hi = atoi(argv[2]);
    int B0 = atoi(argv[3]), B1 = atoi(argv[4]), A0 = atoi(argv[5]);
    int maxm = hi;
    /* odd generalized pentagonal numbers k(3k-1)/2, k in Z, up to 2*maxm, sorted */
    int *ot = malloc(sizeof(int) * (maxm + 10)); int not_ = 0;
    for (long t = 1; t <= 2L * maxm; t++) {
        int ok = 0;
        /* test t = k(3k-1)/2 for integer k: 24t+1 = (6k-1)^2 */
        long d = 24 * t + 1, r = 0; while ((r + 1) * (r + 1) <= d) r++;
        if (r * r == d && (r % 6 == 1 || r % 6 == 5)) ok = 1;
        if (ok && (t % 2)) ot[not_++] = (int)t;
    }
    int *adjstart = malloc(sizeof(int) * (maxm + 2)), *adj = malloc(sizeof(int) * (size_t)maxm * 64);
    int *path = malloc(sizeof(int) * (maxm + 1)), *pos = malloc(sizeof(int) * (maxm + 1));
    int *cand = malloc(sizeof(int) * 128);
    int nfail = 0;
    for (int m = lo; m <= hi; m++) {
        int b = (m % 2 == 0) ? B0 : B1;
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
            int len = 1; path[0] = A0; pos[A0] = 0;
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
