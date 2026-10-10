/* Unmarked broken-stick tetrahedron probability (MO q/142983) by randomised QMC over the 4-simplex.

   By edge-transitivity put the sixth piece t on edge A = 34. For five pieces u (sum 1) and each of the 30
   assignments of u to edges a=12, b=13, C=23, c=14, B=24 (120 bijections modulo the stabiliser {(12),(34)} of
   edge 34), the tetrahedron exists iff faces (a,b,C), (a,c,B) are triangles and t lies in (Amin, Amax), the
   hinge interval. With iid Exp lengths and scaling (see STATUS.md):
       P = E_{u ~ Unif(simplex)} [ sum over disjoint pieces [l, r] of the union of the 30 intervals of
                                   (1+l)^-5 - (1+r)^-5 ].
   Modes: unmarked (union of 30), marked (assignment 0 only: must give 0.01257499441), nomerge (mutant: sums the
   30 intervals without merging overlaps; must be larger), mc (independent indicator Monte Carlo on raw lengths
   via Cayley-Menger and all 30 assignments).
   Points: Sobol (Joe-Kuo direction numbers, dims 1-4) with a random digital shift per replicate; smooth
   stick-breaking map from the cube to the simplex.
   Usage: unmarked MODE log2N REPS SEED */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int perm[30][5]; /* perm[k][e] = index of u placed on edge e, edges ordered a, b, C, c, B */
static int nperm = 0;

static void build_perms(void) {
    /* stabiliser of edge 34 acting on (a,b,C,c,B): (12) swaps b<->C, c<->B; (34) swaps b<->c, C<->B */
    int p[5] = {0, 1, 2, 3, 4};
    int seen[120][5], ns = 0;
    int idx[5];
    for (idx[0] = 0; idx[0] < 5; idx[0]++)
        for (idx[1] = 0; idx[1] < 5; idx[1]++)
            for (idx[2] = 0; idx[2] < 5; idx[2]++)
                for (idx[3] = 0; idx[3] < 5; idx[3]++)
                    for (idx[4] = 0; idx[4] < 5; idx[4]++) {
                        int used = 0, ok = 1;
                        for (int e = 0; e < 5; e++) {
                            if (used >> idx[e] & 1) ok = 0;
                            used |= 1 << idx[e];
                        }
                        if (!ok) continue;
                        /* orbit under the group of order 4 */
                        int g[4][5];
                        for (int e = 0; e < 5; e++) g[0][e] = idx[e];
                        int s12[5] = {0, 2, 1, 4, 3}, s34[5] = {0, 3, 4, 1, 2};
                        for (int e = 0; e < 5; e++) g[1][e] = idx[s12[e]];
                        for (int e = 0; e < 5; e++) g[2][e] = idx[s34[e]];
                        for (int e = 0; e < 5; e++) g[3][e] = idx[s12[s34[e]]];
                        int dup = 0;
                        for (int j = 0; j < ns && !dup; j++)
                            for (int h = 0; h < 4 && !dup; h++)
                                if (!memcmp(seen[j], g[h], sizeof g[h])) dup = 1;
                        if (dup) continue;
                        memcpy(seen[ns++], idx, sizeof idx);
                    }
    (void)p;
    nperm = ns;
    for (int j = 0; j < ns; j++) memcpy(perm[j], seen[j], sizeof perm[j]);
}

/* hinge interval for assignment k; returns 0 if a hinged face is not a triangle */
static int hinge(const double *u, int k, double *lo, double *hi) {
    double a = u[perm[k][0]], b = u[perm[k][1]], C = u[perm[k][2]], c = u[perm[k][3]], B = u[perm[k][4]];
    if (!(b + C > a && a + C > b && a + b > C)) return 0;
    if (!(c + B > a && a + B > c && a + c > B)) return 0;
    double p3 = (a * a + b * b - C * C) / (2 * a), p4 = (a * a + c * c - B * B) / (2 * a);
    double h3 = sqrt(fmax(b * b - p3 * p3, 0)), h4 = sqrt(fmax(c * c - p4 * p4, 0));
    double dp = p3 - p4;
    *lo = sqrt(dp * dp + (h3 - h4) * (h3 - h4));
    *hi = sqrt(dp * dp + (h3 + h4) * (h3 + h4));
    return 1;
}

static double G(double x) {
    double y = 1.0 / (1.0 + x);
    double y2 = y * y;
    return y2 * y2 * y;
}

static int cmp(const void *x, const void *y) {
    double a = *(const double *)x, b = *(const double *)y;
    return (a > b) - (a < b);
}

static double integrand(const double *u, int mode) {
    double iv[30][2];
    int n = 0;
    int K = mode == 1 ? 1 : nperm;
    for (int k = 0; k < K; k++)
        if (hinge(u, k, &iv[n][0], &iv[n][1])) n++;
    if (n == 0) return 0;
    double s = 0;
    if (mode == 2) {
        for (int j = 0; j < n; j++) s += G(iv[j][0]) - G(iv[j][1]);
        return s;
    }
    qsort(iv, n, sizeof iv[0], cmp);
    double l = iv[0][0], r = iv[0][1];
    for (int j = 1; j < n; j++) {
        if (iv[j][0] > r) {
            s += G(l) - G(r);
            l = iv[j][0];
            r = iv[j][1];
        } else if (iv[j][1] > r)
            r = iv[j][1];
    }
    return s + G(l) - G(r);
}

/* Sobol, 4 dims, Joe-Kuo new-joe-kuo-6.21201 */
#define PM 0.0125749944165 /* marked probability from marked.py, +- 2e-13 */
#define BITS 32
static uint32_t V[4][BITS];
static void sobol_init(void) {
    for (int i = 0; i < BITS; i++) V[0][i] = 1u << (31 - i);
    int s[3] = {1, 2, 3}, a[3] = {0, 1, 1};
    int m[3][3] = {{1, 0, 0}, {1, 3, 0}, {1, 3, 1}};
    for (int d = 1; d < 4; d++) {
        int sd = s[d - 1];
        for (int i = 0; i < sd; i++) V[d][i] = (uint32_t)m[d - 1][i] << (31 - i);
        for (int i = sd; i < BITS; i++) {
            V[d][i] = V[d][i - sd] ^ (V[d][i - sd] >> sd);
            for (int k = 1; k < sd; k++)
                if (a[d - 1] >> (sd - 1 - k) & 1) V[d][i] ^= V[d][i - k];
        }
    }
}

static uint64_t rng_state;
static uint64_t rnd(void) { /* splitmix64 */
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}
static double urand(void) { return (rnd() >> 11) * 0x1.0p-53; }

static void to_simplex(const double *v, double *u) {
    /* stick breaking: w1 = v1^(1/4), w2 = v2^(1/3), w3 = v3^(1/2), w4 = v4 gives the uniform simplex */
    double w[4] = {pow(v[0], 0.25), cbrt(v[1]), sqrt(v[2]), v[3]};
    double rest = 1;
    for (int i = 0; i < 4; i++) {
        u[i] = rest * (1 - w[i]);
        rest *= w[i];
    }
    u[4] = rest;
}

static int map_mode = 0; /* 0 stick-breaking, 1 sorted spacings */
static void to_simplex_sp(const double *v, double *u) {
    double t[4] = {v[0], v[1], v[2], v[3]};
    for (int i = 1; i < 4; i++)
        for (int j = i; j > 0 && t[j - 1] > t[j]; j--) {
            double h = t[j]; t[j] = t[j - 1]; t[j - 1] = h;
        }
    u[0] = t[0]; u[1] = t[1] - t[0]; u[2] = t[2] - t[1]; u[3] = t[3] - t[2]; u[4] = 1 - t[3];
}

static int tri(double x, double y, double z) { return x < y + z && y < x + z && z < x + y; }

static int tetra(const double *e) { /* e = a, b, c, A, B, C with (a,A), (b,B), (c,C) opposite */
    double a = e[0], b = e[1], c = e[2], A = e[3], B = e[4], C = e[5];
    if (!(tri(a, b, C) && tri(a, c, B) && tri(b, c, A) && tri(A, B, C))) return 0;
    double a2 = a * a, b2 = b * b, c2 = c * c, A2 = A * A, B2 = B * B, C2 = C * C;
    double cm = a2 * A2 * (b2 + c2 + B2 + C2 - a2 - A2) + b2 * B2 * (a2 + c2 + A2 + C2 - b2 - B2) +
                c2 * C2 * (a2 + b2 + A2 + B2 - c2 - C2) - a2 * b2 * C2 - a2 * c2 * B2 - b2 * c2 * A2 - A2 * B2 * C2;
    return cm > 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s unmarked|marked|nomerge|mc log2N REPS SEED\n", argv[0]);
        return 1;
    }
    int mode = !strcmp(argv[1], "marked") ? 1 : !strcmp(argv[1], "nomerge") ? 2 : !strcmp(argv[1], "mc") ? 3 : !strcmp(argv[1], "smooth") ? 4 : 0;
    int lg = atoi(argv[2]), reps = atoi(argv[3]);
    rng_state = strtoull(argv[4], 0, 10);
    if (argc > 5) map_mode = atoi(argv[5]);
    build_perms();
    if (nperm != 30) {
        fprintf(stderr, "expected 30 assignments, got %d\n", nperm);
        return 2;
    }
    if (!strcmp(argv[1], "perms")) {
        for (int k = 0; k < 30; k++) printf("%d %d %d %d %d\n", perm[k][0], perm[k][1], perm[k][2], perm[k][3], perm[k][4]);
        return 0;
    }
    uint64_t N = 1ull << lg;
    if (mode == 3) { /* indicator MC on raw exponential lengths, all 30 assignments with the sixth on A */
        uint64_t hits = 0;
        for (uint64_t i = 0; i < N; i++) {
            double x[6];
            for (int j = 0; j < 6; j++) x[j] = -log(1 - urand());
            int ok = 0;
            for (int k = 0; k < 30 && !ok; k++) {
                /* edges in tetra() order a, b, c, A, B, C; perm order a, b, C, c, B */
                double e[6] = {x[perm[k][0]], x[perm[k][1]], x[perm[k][3]], x[5], x[perm[k][4]], x[perm[k][2]]};
                ok = tetra(e);
            }
            hits += ok;
        }
        double p = (double)hits / N;
        printf("mc N=2^%d p=%.8f se=%.2e\n", lg, p, sqrt(p * (1 - p) / N));
        return 0;
    }
    sobol_init();
    double sum = 0, sum2 = 0, cvsum = 0, cvsum2 = 0;
    for (int r = 0; r < reps; r++) {
        uint32_t shift[4], x[4] = {0, 0, 0, 0};
        for (int d = 0; d < 4; d++) shift[d] = (uint32_t)rnd();
        double acc = 0, cs = 0, css = 0, cus = 0, cuu = 0;
        for (uint64_t i = 0; i < N; i++) {
            if (i) { /* Gray-code update */
                int c = __builtin_ctzll(i);
                for (int d = 0; d < 4; d++) x[d] ^= V[d][c];
            }
            double v[4], u[5];
            for (int d = 0; d < 4; d++) v[d] = ((x[d] ^ shift[d]) + 0.5) * 0x1.0p-32;
            if (map_mode) to_simplex_sp(v, u); else to_simplex(v, u);
            double fu = mode == 4 ? exp(v[0] + v[1] + v[2] + v[3]) : integrand(u, mode);
            acc += fu;
            if (mode == 0) { /* control variate S = unmerged sum, E[S] = 30 p_m */
                double sv = integrand(u, 2);
                cs += sv; css += sv * sv; cus += fu * sv; cuu += fu * fu;
            }
        }
        double est = acc / N;
        if (mode == 0) {
            double mu = est, ms = cs / N;
            double beta = (cus / N - mu * ms) / (css / N - ms * ms);
            double corr = (cus / N - mu * ms) / sqrt((css / N - ms * ms) * (cuu / N - mu * mu));
            double cv = est - beta * (ms - 30 * PM);
            printf("rep %d plain %.12f cv %.12f beta %.4f corr %.4f\n", r, est, cv, beta, corr);
            cvsum += cv; cvsum2 += cv * cv;
        }
        sum += est;
        sum2 += est * est;
        printf("rep %d %.12f\n", r, est);
        fflush(stdout);
    }
    double mean = sum / reps, var = (sum2 / reps - mean * mean) * reps / (reps - 1);
    printf("%s map=%d N=2^%d reps=%d mean=%.12f se=%.2e\n", argv[1], map_mode, lg, reps, mean, sqrt(var / reps));
    if (mode == 0) {
        double cm = cvsum / reps, cvv = (cvsum2 / reps - cm * cm) * reps / (reps - 1);
        printf("cv map=%d N=2^%d reps=%d mean=%.12f se=%.2e\n", map_mode, lg, reps, cm, sqrt(cvv / reps));
    }
    return 0;
}
