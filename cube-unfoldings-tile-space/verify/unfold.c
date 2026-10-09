/* Unfoldings of the d-cube as polycubes in Z^(d-1), and a lattice-tiling test.
 *
 * Facets of the d-cube: id 2a (+e_a) and 2a+1 (-e_a). Two facets are adjacent
 * unless they are opposite (ids f and f^1). An unfolding is a spanning tree of
 * this facet graph; its polycube is the floor imprint obtained by rolling the
 * cube along the tree (start with facet 2(d-1)+1 face down at the origin).
 *
 * Every labelled spanning tree is generated from a Pruefer sequence and its
 * polycube is reduced modulo the 2^m m! isometries of Z^m (m = d-1). Distinct
 * polycubes are the unfoldings (OEIS A091159: 1, 11, 261, 9694).
 *
 * A polycube P with N = 2d cells tiles Z^m by translations of a lattice L iff
 * [Z^m : L] = N and the cells of P are pairwise distinct mod L. All sublattices
 * of index N are listed in Hermite normal form and tested.
 *
 * Usage: unfold d [certfile] [mutant]
 *   mutant 1: lattice test ignores the last coordinate (must change counts)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXD 5
#define MAXN (2 * MAXD)
#define MAXM (MAXD - 1)

static int D, N, M, MUTANT;

/* ---------- polycube keys ---------- */
typedef struct { uint64_t w[3]; } Key; /* up to 10 cells x 16 bits */

static Key make_key(int cells[][MAXM]) {
    int mn[MAXM];
    uint16_t c[MAXN];
    for (int j = 0; j < M; j++) {
        mn[j] = 1 << 20;
        for (int i = 0; i < N; i++) if (cells[i][j] < mn[j]) mn[j] = cells[i][j];
    }
    for (int i = 0; i < N; i++) {
        uint16_t v = 0;
        for (int j = 0; j < M; j++) v = (uint16_t)(v << 4 | (cells[i][j] - mn[j]));
        c[i] = v;
    }
    for (int i = 1; i < N; i++) { /* insertion sort */
        uint16_t t = c[i]; int k = i - 1;
        while (k >= 0 && c[k] > t) { c[k + 1] = c[k]; k--; }
        c[k + 1] = t;
    }
    Key K = {{0, 0, 0}};
    for (int i = 0; i < N; i++) K.w[i / 4] |= (uint64_t)c[i] << (16 * (i % 4));
    return K;
}

/* ---------- hash set of all isometric images ---------- */
#define HBITS 23
#define HSIZE (1u << HBITS)
typedef struct { Key k; int32_t id; } Slot;
static Slot *H;

static uint32_t hk(Key k) {
    uint64_t h = k.w[0] * 0x9E3779B97F4A7C15ull ^ k.w[1] * 0xC2B2AE3D27D4EB4Full ^ k.w[2] * 0x165667B19E3779F9ull;
    h ^= h >> 29;
    return (uint32_t)(h & (HSIZE - 1));
}
static int keq(Key a, Key b) { return a.w[0] == b.w[0] && a.w[1] == b.w[1] && a.w[2] == b.w[2]; }
static int hfind(Key k) {
    for (uint32_t i = hk(k);; i = (i + 1) & (HSIZE - 1)) {
        if (H[i].id < 0) return -1;
        if (keq(H[i].k, k)) return H[i].id;
    }
}
static void hput(Key k, int id) {
    for (uint32_t i = hk(k);; i = (i + 1) & (HSIZE - 1)) {
        if (H[i].id < 0) { H[i].k = k; H[i].id = id; return; }
        if (keq(H[i].k, k)) return;
    }
}

/* ---------- isometries of Z^m ---------- */
static int NISO, iso_perm[384][MAXM], iso_sign[384][MAXM];
static void gen_isos(void) {
    int p[MAXM];
    for (int i = 0; i < M; i++) p[i] = i;
    NISO = 0;
    for (;;) {
        for (int s = 0; s < (1 << M); s++) {
            for (int i = 0; i < M; i++) { iso_perm[NISO][i] = p[i]; iso_sign[NISO][i] = (s >> i & 1) ? -1 : 1; }
            NISO++;
        }
        int i = M - 2; /* next permutation */
        while (i >= 0 && p[i] > p[i + 1]) i--;
        if (i < 0) break;
        int j = M - 1;
        while (p[j] < p[i]) j--;
        int t = p[i]; p[i] = p[j]; p[j] = t;
        for (int a = i + 1, b = M - 1; a < b; a++, b--) { t = p[a]; p[a] = p[b]; p[b] = t; }
    }
}

/* ---------- representatives ---------- */
#define MAXREP 20000
static int NREP, rep_cells[MAXREP][MAXN][MAXM], rep_linear[MAXREP];
static long rep_trees[MAXREP];

/* ---------- rolling ---------- */
static int adjn[MAXN][MAXN], deg[MAXN];
static int cells[MAXN][MAXM], ncell;

/* orientation: cube axis a points to world axis w[a] with sign s[a];
   world axis M is vertical. */
static void roll(int f, int parent, int *w, int *s, int *pos) {
    for (int j = 0; j < M; j++) cells[ncell][j] = pos[j];
    ncell++;
    for (int e = 0; e < deg[f]; e++) {
        int g = adjn[f][e];
        if (g == parent) continue;
        int a = g >> 1, sg = (g & 1) ? -1 : 1;
        int k = w[a], dir = sg * s[a]; /* g faces world dir*e_k, k horizontal */
        int w2[MAXD], s2[MAXD], pos2[MAXM];
        for (int b = 0; b < D; b++) {
            w2[b] = w[b]; s2[b] = s[b];
            /* rolling toward dir*e_k: dir*e_k -> -e_v, e_v -> dir*e_k */
            if (w[b] == k) { w2[b] = M; s2[b] = -s[b] * dir; }
            else if (w[b] == M) { w2[b] = k; s2[b] = s[b] * dir; }
        }
        memcpy(pos2, pos, sizeof pos2);
        pos2[k] += dir;
        roll(g, f, w2, s2, pos2);
    }
}

static long ntrees;
static void process_tree(int edges[][2]) {
    memset(deg, 0, sizeof deg);
    int linear = 1;
    for (int i = 0; i < N - 1; i++) {
        int u = edges[i][0], v = edges[i][1];
        adjn[u][deg[u]++] = v;
        adjn[v][deg[v]++] = u;
    }
    for (int i = 0; i < N; i++) if (deg[i] > 2) linear = 0;
    ntrees++;
    int w[MAXD], s[MAXD], pos[MAXM] = {0};
    for (int b = 0; b < D; b++) { w[b] = b; s[b] = 1; }
    ncell = 0;
    roll(2 * (D - 1) + 1, -1, w, s, pos); /* facet -e_{d-1} faces down */
    Key k = make_key(cells);
    int id = hfind(k);
    if (id < 0) {
        /* new unfolding: check cells distinct, store all isometric images */
        for (int i = 0; i < N; i++)
            for (int j = i + 1; j < N; j++)
                if (!memcmp(cells[i], cells[j], sizeof(int) * M)) { fprintf(stderr, "overlap!\n"); exit(2); }
        id = NREP++;
        if (NREP > MAXREP) { fprintf(stderr, "too many reps\n"); exit(2); }
        memcpy(rep_cells[id], cells, sizeof cells);
        int img[MAXN][MAXM];
        for (int t = 0; t < NISO; t++) {
            for (int i = 0; i < N; i++)
                for (int j = 0; j < M; j++) img[i][j] = iso_sign[t][j] * cells[i][iso_perm[t][j]];
            hput(make_key(img), id);
        }
    }
    rep_trees[id]++;
    if (linear) rep_linear[id] = 1;
}

/* Pruefer enumeration of spanning trees of K_N avoiding opposite pairs */
static void enum_trees(void) {
    int seq[MAXN], degc[MAXN], edges[MAXN][2];
    long total = 1;
    for (int i = 0; i < N - 2; i++) total *= N;
    for (long x = 0; x < total; x++) {
        long y = x;
        for (int i = 0; i < N - 2; i++) { seq[i] = (int)(y % N); y /= N; }
        for (int i = 0; i < N; i++) degc[i] = 1;
        for (int i = 0; i < N - 2; i++) degc[seq[i]]++;
        int ok = 1, ne = 0;
        for (int i = 0; i < N - 2 && ok; i++) {
            int leaf = 0;
            while (degc[leaf] != 1) leaf++;
            int v = seq[i];
            if ((leaf ^ 1) == v) ok = 0;
            edges[ne][0] = leaf; edges[ne][1] = v; ne++;
            degc[leaf]--; degc[v]--;
        }
        if (!ok) continue;
        int u = -1, v = -1;
        for (int i = 0; i < N; i++) if (degc[i] == 1) { if (u < 0) u = i; else v = i; }
        if ((u ^ 1) == v) continue;
        edges[ne][0] = u; edges[ne][1] = v;
        process_tree(edges);
    }
}

/* ---------- sublattices of index N in Z^M, Hermite normal form ---------- */
#define MAXLAT 4000
static int NLAT, lat[MAXLAT][MAXM][MAXM]; /* rows; upper triangular */
static void gen_lat_rec(int i, int rem, int B[MAXM][MAXM]) {
    if (i == M) {
        if (rem != 1) return;
        /* off-diagonal entries: B[r][j] for j > r in [0, B[j][j]) */
        int slots[MAXM * MAXM][2], ns = 0;
        for (int r = 0; r < M; r++) for (int j = r + 1; j < M; j++) { slots[ns][0] = r; slots[ns][1] = j; ns++; }
        int idx[MAXM * MAXM] = {0};
        for (;;) {
            for (int t = 0; t < ns; t++) B[slots[t][0]][slots[t][1]] = idx[t];
            if (NLAT >= MAXLAT) { fprintf(stderr, "too many lattices\n"); exit(2); }
            memcpy(lat[NLAT++], B, sizeof(int) * MAXM * MAXM);
            int t = 0;
            while (t < ns && ++idx[t] == B[slots[t][1]][slots[t][1]]) idx[t++] = 0;
            if (t == ns) break;
        }
        return;
    }
    for (int d = 1; d <= rem; d++)
        if (rem % d == 0) {
            for (int j = 0; j < M; j++) B[i][j] = 0;
            B[i][i] = d;
            gen_lat_rec(i + 1, rem / d, B);
        }
}

static int floordiv(int a, int b) { return a >= 0 ? a / b : -((-a + b - 1) / b); }

/* coset representative of v mod lattice t, packed into an int */
static int coset(int t, const int *v0) {
    int v[MAXM];
    memcpy(v, v0, sizeof v);
    for (int i = 0; i < M; i++) {
        int q = floordiv(v[i], lat[t][i][i]);
        for (int j = i; j < M; j++) v[j] -= q * lat[t][i][j];
    }
    int c = 0;
    int top = MUTANT == 1 ? M - 1 : M;
    for (int i = 0; i < top; i++) c = c * 16 + v[i];
    return c;
}

static int tiles_by_lattice(int r) {
    for (int t = 0; t < NLAT; t++) {
        int cs[MAXN], ok = 1;
        for (int i = 0; i < N && ok; i++) {
            cs[i] = coset(t, rep_cells[r][i]);
            for (int j = 0; j < i; j++) if (cs[j] == cs[i]) { ok = 0; break; }
        }
        if (ok) return t;
    }
    return -1;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: unfold d [certfile] [mutant]\n"); return 1; }
    D = atoi(argv[1]);
    if (D < 2 || D > MAXD) return 1;
    N = 2 * D; M = D - 1;
    MUTANT = argc > 3 ? atoi(argv[3]) : 0;
    H = malloc(sizeof(Slot) * HSIZE);
    for (uint32_t i = 0; i < HSIZE; i++) H[i].id = -1;
    gen_isos();
    enum_trees();
    int B[MAXM][MAXM];
    gen_lat_rec(0, N, B);
    int nlin = 0, ntile = 0, nlintile = 0;
    FILE *cf = argc > 2 ? fopen(argv[2], "w") : NULL;
    for (int r = 0; r < NREP; r++) {
        int t = tiles_by_lattice(r);
        nlin += rep_linear[r];
        if (t >= 0) { ntile++; nlintile += rep_linear[r]; }
        if (cf) {
            fprintf(cf, "%d linear=%d cells=", r, rep_linear[r]);
            for (int i = 0; i < N; i++) {
                fprintf(cf, "(");
                for (int j = 0; j < M; j++) fprintf(cf, "%d%s", rep_cells[r][i][j], j < M - 1 ? "," : "");
                fprintf(cf, ")");
            }
            if (t >= 0) {
                fprintf(cf, " lattice=");
                for (int i = 0; i < M; i++) {
                    fprintf(cf, "[");
                    for (int j = 0; j < M; j++) fprintf(cf, "%d%s", lat[t][i][j], j < M - 1 ? "," : "");
                    fprintf(cf, "]");
                }
            } else fprintf(cf, " lattice=none");
            fprintf(cf, "\n");
        }
    }
    if (cf) fclose(cf);
    printf("d=%d trees=%ld unfoldings=%d linear=%d isometries=%d sublattices=%d lattice_tilers=%d linear_lattice_tilers=%d\n",
           D, ntrees, NREP, nlin, NISO, NLAT, ntile, nlintile);
    return 0;
}
