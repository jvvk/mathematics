/* Point-reflection tilings, fast version for d <= 6.
 *
 * P and -P + t tile Z^m periodically with one copy of each per period iff there is a
 * homomorphism phi from Z^m onto an abelian group G of order 4d, injective on P, with
 * phi(P) and s - phi(P) complementary for some s in G (Lemma 2 of the paper). With
 * A = phi(P), |A| = |G|/2, the set s - A misses A exactly when s is not a sum a + a' of two
 * elements of A. So the test is:  phi onto,  |A| = 2d,  A + A != G.  Any s outside A + A works.
 *
 * Homomorphisms are enumerated by the images of e_1..e_m, nested, with partial cell images
 * kept per level and a collision check at every level (two cells that agree in the remaining
 * coordinates must already differ). The first solution found is reported.
 *
 * Usage: inv d certfile outfile [first last]
 * Output lines match stage2.c: "id proper|reflection group=.. phi=(..).. g=perm..,sign--.."
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXD 6
#define MAXN (2 * MAXD)
#define MAXM (MAXD - 1)
#define MAXG 64

static int D, N, M, NG;
static int nf, fac[MAXM];
static int addt[MAXG][MAXG], negt[MAXG], mult[MAXG][MAXG];

static void decode(int x, int *c) { for (int i = nf - 1; i >= 0; i--) { c[i] = x % fac[i]; x /= fac[i]; } }
static int encode(const int *c) { int x = 0; for (int i = 0; i < nf; i++) x = x * fac[i] + c[i]; return x; }

static void build_group(void) {
    int a[MAXM], b[MAXM], c[MAXM];
    for (int x = 0; x < NG; x++) {
        decode(x, a);
        for (int i = 0; i < nf; i++) c[i] = (fac[i] - a[i]) % fac[i];
        negt[x] = encode(c);
        for (int y = 0; y < NG; y++) {
            decode(y, b);
            for (int i = 0; i < nf; i++) c[i] = (a[i] + b[i]) % fac[i];
            addt[x][y] = encode(c);
        }
    }
    for (int x = 0; x < NG; x++) { /* needs the whole addition table */
        mult[x][0] = 0;
        for (int k = 1; k < NG; k++) mult[x][k] = addt[mult[x][k - 1]][x];
    }
}

static int ntypes, types[16][MAXM + 1];
static void gen_types(int n, int prev, int k, int *cur) {
    if (n == 1) {
        types[ntypes][0] = k;
        for (int i = 0; i < k; i++) types[ntypes][1 + i] = cur[k - 1 - i];
        ntypes++;
        return;
    }
    if (k == M) return;
    for (int f = 2; f <= n; f++)
        if (n % f == 0 && (k == 0 || prev % f == 0)) { cur[k] = f; gen_types(n / f, f, k + 1, cur); }
}

static int onto(const int *a) {
    uint64_t span = 1, prev = 0;
    while (span != prev) {
        prev = span;
        for (uint64_t q = prev; q; q &= q - 1)
            for (int j = 0; j < M; j++) span |= 1ull << addt[__builtin_ctzll(q)][a[j]];
    }
    return __builtin_popcountll(span) == NG;
}

/* ---------- search ---------- */
static int cm[MAXN][MAXM];          /* cell coordinates mod NG */
static int part[MAXM + 1][MAXN];    /* partial images after fixing a_0..a_{j-1} */
static int same[MAXM + 1][MAXN][MAXN]; /* same[j][i][k]: cells i,k agree in coords j..M-1 */
static int a[MAXM], found;
static uint64_t full;
static long nhoms;

static void rec(int j) {
    if (found) return;
    if (j == M) {
        nhoms++;
        uint64_t A = 0;
        for (int i = 0; i < N; i++) A |= 1ull << part[M][i];
        if (__builtin_popcountll(A) != N) return;
        uint64_t S = 0;
        for (uint64_t p = A; p; p &= p - 1) {
            int x = __builtin_ctzll(p);
            for (uint64_t q = p; q; q &= q - 1) S |= 1ull << addt[x][__builtin_ctzll(q)];
        }
        if (S != full && onto(a)) found = 1;
        return;
    }
    for (int v = 0; v < NG && !found; v++) {
        a[j] = v;
        int ok = 1;
        for (int i = 0; i < N; i++) part[j + 1][i] = addt[part[j][i]][mult[v][cm[i][j]]];
        /* cells agreeing in the remaining coordinates must already have distinct images */
        for (int i = 0; i < N && ok; i++)
            for (int k = i + 1; k < N; k++)
                if (same[j + 1][i][k] && part[j + 1][i] == part[j + 1][k]) { ok = 0; break; }
        if (ok) rec(j + 1);
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: inv d certfile outfile [first last]\n"); return 1; }
    D = atoi(argv[1]); N = 2 * D; M = D - 1; NG = 2 * N;
    full = NG == 64 ? ~0ull : (1ull << NG) - 1;
    int cur[MAXM];
    gen_types(NG, 0, 0, cur);
    FILE *f = fopen(argv[2], "r"), *out = fopen(argv[3], "a");
    if (!f || !out) { perror("open"); return 1; }
    long first = argc > 5 ? atol(argv[4]) : 0, last = argc > 5 ? atol(argv[5]) : -1;
    char line[4096];
    long u = -1, done = 0, ok = 0, maxhoms = 0;
    while (fgets(line, sizeof line, f)) {
        u++;
        if (u < first || (last >= 0 && u >= last)) continue;
        long id = atol(line);
        int cells[MAXN][MAXM];
        char *p = strstr(line, "cells=") + 6;
        for (int i = 0; i < N; i++) {
            p = strchr(p, '(') + 1;
            for (int j = 0; j < M; j++) { cells[i][j] = (int)strtol(p, &p, 10); p++; }
        }
        for (int j = 0; j <= M; j++)
            for (int i = 0; i < N; i++)
                for (int k = 0; k < N; k++) {
                    int s = 1;
                    for (int t = j; t < M; t++) s &= cells[i][t] == cells[k][t];
                    same[j][i][k] = s;
                }
        for (int i = 0; i < N; i++)
            for (int j = 0; j < M; j++) cm[i][j] = ((cells[i][j] % NG) + NG) % NG;
        found = 0;
        int wt = -1;
        long homs = 0;
        for (int t = 0; t < ntypes && !found; t++) {
            nf = types[t][0];
            for (int i = 0; i < nf; i++) fac[i] = types[t][1 + i];
            build_group();
            memset(part[0], 0, sizeof part[0]);
            nhoms = 0;
            rec(0);
            homs += nhoms;
            if (found) wt = t;
        }
        if (homs > maxhoms) maxhoms = homs;
        done++;
        /* -I has determinant (-1)^M */
        fprintf(out, "%ld %s", id, found ? ((M % 2 == 0) ? "proper" : "reflection") : "none");
        if (found) {
            fprintf(out, " group=");
            for (int i = 0; i < nf; i++) fprintf(out, "%d%s", fac[i], i < nf - 1 ? "x" : "");
            fprintf(out, " phi=");
            int c[MAXM];
            for (int j = 0; j < M; j++) {
                decode(a[j], c);
                fprintf(out, "(");
                for (int i = 0; i < nf; i++) fprintf(out, "%d%s", c[i], i < nf - 1 ? "," : "");
                fprintf(out, ")");
            }
            fprintf(out, " g=perm");
            for (int j = 0; j < M; j++) fprintf(out, "%d", j);
            fprintf(out, ",sign");
            for (int j = 0; j < M; j++) fprintf(out, "-");
            ok++;
        }
        (void)wt;
        fprintf(out, "\n");
        fflush(out); /* a chunk killed by its CPU cap must not leave a half-written line */
    }
    fclose(out);
    printf("d=%d group_types=%d processed=%ld tiled=%ld none=%ld max_homs_tried=%ld\n", D, ntypes, done, ok, done - ok, maxhoms);
    return 0;
}
