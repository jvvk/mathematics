/* Stage 2: periodic tilings with two tiles per period.
 *
 * A tiling of Z^m by P and an isometric copy gP + t, periodic under a lattice L
 * of index 2N, is the same as a surjective homomorphism phi: Z^m -> G (|G| = 2N,
 * L = ker phi) with phi(P) and phi(gP) + s disjoint and together all of G.
 * Since phi(gP) = (phi o g)(P), write C(psi) for the set psi(P) up to
 * translation in G. A solution is a pair (phi, g) with |phi(P)| = N and
 * C(complement of phi(P)) = C(phi o g). Non-surjective phi cannot occur here:
 * it would make P a lattice tiler; onto() rejects it, so lattice tilers may be read too.
 *
 * Every abelian G of order 2N with at most m invariant factors is tried.
 *
 * Usage: stage2 d certfile outfile [first last]
 * Environment ONLY_INVERSION=1 restricts the second copy to -P + t.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXD 5
#define MAXN 10
#define MAXM 4
#define MAXG 64

static int D, N, M, NG, ONLY_INVERSION;
static int NISO, iso_perm[384][MAXM], iso_sign[384][MAXM], iso_det[384];

static void gen_isos(void) {
    int p[MAXM];
    for (int i = 0; i < M; i++) p[i] = i;
    NISO = 0;
    for (;;) {
        int inv = 0;
        for (int a = 0; a < M; a++)
            for (int b = a + 1; b < M; b++) inv += p[a] > p[b];
        for (int s = 0; s < (1 << M); s++) {
            int det = inv & 1 ? -1 : 1;
            for (int i = 0; i < M; i++) {
                iso_perm[NISO][i] = p[i];
                iso_sign[NISO][i] = (s >> i & 1) ? -1 : 1;
                det *= iso_sign[NISO][i];
            }
            iso_det[NISO++] = det;
        }
        int i = M - 2;
        while (i >= 0 && p[i] > p[i + 1]) i--;
        if (i < 0) break;
        int j = M - 1;
        while (p[j] < p[i]) j--;
        int t = p[i]; p[i] = p[j]; p[j] = t;
        for (int a = i + 1, b = M - 1; a < b; a++, b--) { t = p[a]; p[a] = p[b]; p[b] = t; }
    }
}

/* ---------- groups Z_{f0} x ... x Z_{fk-1}, f0 | f1 | ... ---------- */
static int nf, fac[MAXM];
static int addt[MAXG][MAXG], negt[MAXG], mult[MAXG][MAXG]; /* mult[x][k] = k*x, k in [0, NG) */

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

/* all invariant-factor lists of order n with at most M factors */
static int ntypes, types[16][MAXM + 1]; /* types[t][0] = count */
static void gen_types(int n, int prev, int k, int *cur) {
    /* build from the largest factor down: cur[0] is the largest */
    if (n == 1) {
        if (ntypes >= 16) return;
        types[ntypes][0] = k;
        for (int i = 0; i < k; i++) types[ntypes][1 + i] = cur[k - 1 - i]; /* ascending, each divides next */
        ntypes++;
        return;
    }
    if (k == M) return;
    for (int f = 2; f <= n; f++)
        if (n % f == 0 && (k == 0 || prev % f == 0)) {
            cur[k] = f;
            gen_types(n / f, f, k + 1, cur);
        }
}

/* ---------- unfoldings ---------- */
static int NU, uid[20000], ucell[20000][MAXN][MAXM];

static void read_certs(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(1); }
    char line[4096];
    NU = 0;
    while (fgets(line, sizeof line, f)) {
        if (!strstr(line, "lattice=none")) continue;
        int id;
        sscanf(line, "%d", &id);
        char *p = strstr(line, "cells=") + 6;
        for (int i = 0; i < N; i++) {
            p = strchr(p, '(') + 1;
            for (int j = 0; j < M; j++) {
                ucell[NU][i][j] = (int)strtol(p, &p, 10);
                p++;
            }
        }
        uid[NU++] = id;
    }
    fclose(f);
}

/* ---------- search ---------- */
static uint64_t *canonP; /* per hom: canonical mask of phi(P), 0 if not injective */
static int ipow(int b, int e) { int r = 1; while (e--) r *= b; return r; }

static uint64_t canon_of(uint64_t mask) {
    uint64_t best = ~0ull;
    for (uint64_t mm = mask; mm; mm &= mm - 1) {
        int x = __builtin_ctzll(mm), nx = negt[x];
        uint64_t sh = 0;
        for (uint64_t q = mask; q; q &= q - 1) sh |= 1ull << addt[__builtin_ctzll(q)][nx];
        if (sh < best) best = sh;
    }
    return best;
}

/* is phi (images a[0..M-1]) onto G? */
static int onto(const int *a) {
    uint64_t span = 1, prev = 0; /* bit 0 = identity */
    while (span != prev) {
        prev = span;
        for (uint64_t q = prev; q; q &= q - 1)
            for (int j = 0; j < M; j++) span |= 1ull << addt[__builtin_ctzll(q)][a[j]];
    }
    return __builtin_popcountll(span) == NG;
}

/* returns 1 and fills witness if unfolding u has a 2-tile periodic tiling with group type */
static int search(int u, int *wh, int *wg, int want_proper) {
    int nh = ipow(NG, M);
    int cm[MAXN][MAXM]; /* coordinates mod NG, nonnegative */
    for (int i = 0; i < N; i++)
        for (int j = 0; j < M; j++) cm[i][j] = ((ucell[u][i][j] % NG) + NG) % NG;
    int a[MAXM];
    for (int h = 0; h < nh; h++) {
        int x = h;
        for (int j = 0; j < M; j++) { a[j] = x % NG; x /= NG; }
        uint64_t mask = 0;
        for (int i = 0; i < N; i++) {
            int v = 0;
            for (int j = 0; j < M; j++) v = addt[v][mult[a[j]][cm[i][j]]];
            mask |= 1ull << v;
        }
        canonP[h] = __builtin_popcountll(mask) == N ? canon_of(mask) : 0;
    }
    uint64_t full = NG == 64 ? ~0ull : (1ull << NG) - 1;
    for (int h = 0; h < nh; h++) {
        if (!canonP[h]) continue;
        int x = h;
        for (int j = 0; j < M; j++) { a[j] = x % NG; x /= NG; }
        /* recompute raw mask for the complement */
        uint64_t mask = 0;
        for (int i = 0; i < N; i++) {
            int v = 0;
            for (int j = 0; j < M; j++) v = addt[v][mult[a[j]][cm[i][j]]];
            mask |= 1ull << v;
        }
        uint64_t cc = canon_of(full & ~mask);
        for (int g = 0; g < NISO; g++) {
            if (want_proper && iso_det[g] < 0) continue;
            if (ONLY_INVERSION) { /* restrict to g = -I */
                int inv = 1;
                for (int j = 0; j < M; j++) inv &= iso_perm[g][j] == j && iso_sign[g][j] < 0;
                if (!inv) continue;
            }
            /* (phi o g)(e_j) = phi(sign_j e_{perm_j}) */
            int h2 = 0;
            for (int j = M - 1; j >= 0; j--) {
                int img = a[iso_perm[g][j]];
                if (iso_sign[g][j] < 0) img = negt[img];
                h2 = h2 * NG + img;
            }
            if (canonP[h2] == cc && onto(a)) { *wh = h; *wg = g; return 1; }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: stage2 d certfile outfile [first last]\n"); return 1; }
    D = atoi(argv[1]); N = 2 * D; M = D - 1; NG = 2 * N;
    ONLY_INVERSION = getenv("ONLY_INVERSION") != NULL;
    gen_isos();
    read_certs(argv[2]);
    int first = argc > 5 ? atoi(argv[4]) : 0, last = argc > 5 ? atoi(argv[5]) : NU;
    if (last > NU) last = NU;
    int cur[MAXM];
    gen_types(NG, 0, 0, cur);
    canonP = malloc(sizeof(uint64_t) * ipow(NG, M));
    FILE *out = fopen(argv[3], "a");
    int found = 0, proper = 0;
    for (int u = first; u < last; u++) {
        int ok = 0, okp = 0, wh = -1, wg = -1, wt = -1;
        for (int t = 0; t < ntypes && !okp; t++) {
            nf = types[t][0];
            for (int i = 0; i < nf; i++) fac[i] = types[t][1 + i];
            build_group();
            int h, g;
            if (search(u, &h, &g, 1)) { ok = okp = 1; wh = h; wg = g; wt = t; }
            else if (!ok && search(u, &h, &g, 0)) { ok = 1; wh = h; wg = g; wt = t; }
        }
        found += ok; proper += okp;
        fprintf(out, "%d %s", uid[u], ok ? (okp ? "proper" : "reflection") : "none");
        if (ok) {
            nf = types[wt][0];
            for (int i = 0; i < nf; i++) fac[i] = types[wt][1 + i];
            fprintf(out, " group=");
            for (int i = 0; i < nf; i++) fprintf(out, "%d%s", fac[i], i < nf - 1 ? "x" : "");
            fprintf(out, " phi=");
            int x = wh, c[MAXM];
            for (int j = 0; j < M; j++) {
                decode(x % NG, c); x /= NG;
                fprintf(out, "(");
                for (int i = 0; i < nf; i++) fprintf(out, "%d%s", c[i], i < nf - 1 ? "," : "");
                fprintf(out, ")");
            }
            fprintf(out, " g=perm");
            for (int j = 0; j < M; j++) fprintf(out, "%d", iso_perm[wg][j]);
            fprintf(out, ",sign");
            for (int j = 0; j < M; j++) fprintf(out, "%c", iso_sign[wg][j] > 0 ? '+' : '-');
        }
        fprintf(out, "\n");
        fflush(out);
    }
    fclose(out);
    printf("d=%d group_types=%d read=%d range=[%d,%d) two_tile=%d proper=%d\n", D, ntypes, NU, first, last, found, proper);
    return 0;
}
