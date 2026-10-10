/* MSE q/2060312. A = {r + 2^k e_r : r < 2^k}, B = {r + 2^k f_r}, e, f bit vectors, in Z/2^(k+1).
   Is there a bijection sigma with a_r + b_sigma(r) pairwise distinct?  Exhaustive over (e, f) for k <= 3,
   with the symmetry e_0 = 0 (translate A by 2^k) and f_0 = 0; random sampling for k = 4, 5.
   Usage: pairing K [samples] [mutant]  (mutant 1: distinctness only mod 2^k, which must fail by Hall-Paige). */
#include <stdio.h>
#include <stdlib.h>
static int K, N, M, MUT;
static int a[64], b[64], used[64], hit[128];
static long long nodes;
static int rec(int r) {
    if (r == N) return 1;
    for (int s = 0; s < N; s++) {
        if (used[s]) continue;
        int v = (a[r] + b[s]) % (MUT ? N : M);
        if (hit[v]) continue;
        used[s] = 1; hit[v] = 1; nodes++;
        if (rec(r + 1)) { used[s] = 0; hit[v] = 0; return 1; }
        used[s] = 0; hit[v] = 0;
    }
    return 0;
}
static unsigned long long rng = 88172645463325252ULL;
static unsigned long long xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
int main(int argc, char **argv) {
    K = atoi(argv[1]); N = 1 << K; M = 2 * N;
    long long samples = argc > 2 ? atoll(argv[2]) : 0; MUT = argc > 3 ? atoi(argv[3]) : 0;
    long long tried = 0, fails = 0;
    if (samples == 0) {
        for (long long e = 0; e < (1LL << N); e += 2)
            for (long long f = 0; f < (1LL << N); f += 2) {
                for (int r = 0; r < N; r++) { a[r] = r + N * ((e >> r) & 1); b[r] = r + N * ((f >> r) & 1); }
                tried++;
                if (!rec(0)) { fails++; if (fails <= 3) printf("no pairing: e=%llx f=%llx\n", e, f); }
            }
    } else {
        for (long long t = 0; t < samples; t++) {
            unsigned long long e = xr(), f = xr();
            for (int r = 0; r < N; r++) { a[r] = r + N * ((e >> r) & 1); b[r] = r + N * ((f >> r) & 1); }
            tried++;
            if (!rec(0)) { fails++; if (fails <= 3) printf("no pairing: e=%llx f=%llx\n", e, f); }
        }
    }
    printf("k=%d: %lld pairs (A,B) tried, %lld without a pairing, %lld search nodes\n", K, tried, fails, nodes);
    return fails ? 1 : 0;
}
