/* MO q/487157: which n-ominoes tile the n x n square with n copies (rotations and reflections allowed)?
   Question: for prime p, is the 1 x p bar the only one?

   1. Enumerate fixed n-ominoes (Redelmeier), keep one per free class (canonical form = min over the 8 symmetries).
   2. For each free n-omino fitting in n x n, backtrack: the first empty cell in row-major order must be the
      row-major-first cell of some placed orientation.
   Output: free count, then every n-omino that tiles, as a picture of one tiling.
   Usage: tilesq N [mutant]   (mutant: forbid reflections, a strictly weaker search, for the control) */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 17
static int N, MUT = 0;
typedef struct {
    int x[MAXN], y[MAXN];
} Poly;

/* ---------- canonical form ---------- */
static int cmp_cell(const void *a, const void *b) {
    const int *p = a, *q = b;
    return p[1] != q[1] ? p[1] - q[1] : p[0] - q[0]; /* row-major: y then x */
}
static void normalize(int *c, int n) { /* c = x0,y0,x1,y1,...; translate to min 0 and sort */
    int mx = 1 << 30, my = 1 << 30;
    for (int i = 0; i < n; i++) mx = c[2 * i] < mx ? c[2 * i] : mx, my = c[2 * i + 1] < my ? c[2 * i + 1] : my;
    for (int i = 0; i < n; i++) c[2 * i] -= mx, c[2 * i + 1] -= my;
    qsort(c, n, 2 * sizeof(int), cmp_cell);
}
static void orient(const int *src, int *dst, int n, int o) {
    for (int i = 0; i < n; i++) {
        int x = src[2 * i], y = src[2 * i + 1], a, b;
        switch (o & 3) {
        case 0: a = x, b = y; break;
        case 1: a = -y, b = x; break;
        case 2: a = -x, b = -y; break;
        default: a = y, b = -x;
        }
        if (o & 4) a = -a;
        dst[2 * i] = a, dst[2 * i + 1] = b;
    }
    normalize(dst, n);
}
static int is_canonical(const int *c, int n) {
    int t[2 * MAXN];
    for (int o = 1; o < 8; o++) {
        orient(c, t, n, o);
        for (int i = 0; i < 2 * n; i++) /* lexicographic compare on the int sequence */
            if (t[i] != c[i]) {
                if (t[i] < c[i]) return 0;
                break;
            }
    }
    return 1;
}

/* ---------- tiling test ---------- */
static int npl;                /* number of distinct orientations */
static int pl[8][MAXN][2];     /* cells relative to the orientation's first cell */
static int grid[MAXN * MAXN];  /* 0 empty, k = tile id */
static int sol[MAXN * MAXN];

static int place_rec(int placed) {
    if (placed == N) return 1;
    int f = 0;
    while (grid[f]) f++;
    int fy = f / N, fx = f % N;
    for (int o = 0; o < npl; o++) {
        int ok = 1;
        for (int i = 0; i < N && ok; i++) {
            int x = fx + pl[o][i][0], y = fy + pl[o][i][1];
            if (x < 0 || x >= N || y < 0 || y >= N || grid[y * N + x]) ok = 0;
        }
        if (!ok) continue;
        for (int i = 0; i < N; i++) grid[(fy + pl[o][i][1]) * N + fx + pl[o][i][0]] = placed + 1;
        if (place_rec(placed + 1)) return 1;
        for (int i = 0; i < N; i++) grid[(fy + pl[o][i][1]) * N + fx + pl[o][i][0]] = 0;
    }
    return 0;
}

static long long nfree = 0, ntile = 0;

static void test_poly(const int *c) {
    /* bounding box must fit */
    int w = 0, h = 0;
    for (int i = 0; i < N; i++) w = c[2 * i] > w ? c[2 * i] : w, h = c[2 * i + 1] > h ? c[2 * i + 1] : h;
    if (w >= N || h >= N) return;
    npl = 0;
    int seen[8][2 * MAXN];
    int no = MUT ? 1 : 8; /* mutant: translations only */
    for (int o = 0; o < no; o++) {
        int t[2 * MAXN];
        orient(c, t, N, o);
        int dup = 0;
        for (int j = 0; j < npl && !dup; j++)
            if (!memcmp(seen[j], t, 2 * N * sizeof(int))) dup = 1;
        if (dup) continue;
        memcpy(seen[npl], t, 2 * N * sizeof(int));
        /* first cell in row-major order is t[0], t[1] after normalize */
        for (int i = 0; i < N; i++) pl[npl][i][0] = t[2 * i] - t[0], pl[npl][i][1] = t[2 * i + 1] - t[1];
        npl++;
    }
    memset(grid, 0, sizeof(int) * N * N);
    if (place_rec(0)) {
        ntile++;
        printf("TILES:");
        for (int i = 0; i < N; i++) printf(" (%d,%d)", c[2 * i], c[2 * i + 1]);
        printf("\n");
        for (int y = 0; y < N; y++) {
            for (int x = 0; x < N; x++) printf("%c", 'a' + (grid[y * N + x] - 1) % 26);
            printf("\n");
        }
        fflush(stdout);
    }
}

/* ---------- Redelmeier enumeration of fixed polyominoes ---------- */
#define W (2 * MAXN + 2)
static unsigned char used[W * 2 * W];
static int cells[MAXN][2];

static void emit(int n) {
    int c[2 * MAXN];
    for (int i = 0; i < n; i++) c[2 * i] = cells[i][0], c[2 * i + 1] = cells[i][1];
    normalize(c, n);
    if (!is_canonical(c, n)) return;
    nfree++;
    test_poly(c);
}

static int idx(int x, int y) { return (y + 1) * W + (x + MAXN + 1); }

static void redel(int n, int *untried, int nun) {
    while (nun > 0) {
        int u = untried[--nun];
        int x = u % W - (MAXN + 1), y = u / W - 1;
        cells[n][0] = x, cells[n][1] = y;
        if (n + 1 == N) {
            emit(n + 1);
            continue;
        }
        int nu[4 * MAXN + 4], k = nun;
        memcpy(nu, untried, nun * sizeof(int));
        int added[4], na = 0;
        int dx[4] = {1, -1, 0, 0}, dy[4] = {0, 0, 1, -1};
        for (int d = 0; d < 4; d++) {
            int xx = x + dx[d], yy = y + dy[d];
            if (yy < 0 || (yy == 0 && xx < 0)) continue;
            int id = idx(xx, yy);
            if (used[id]) continue;
            used[id] = 1;
            added[na++] = id;
            nu[k++] = id;
        }
        redel(n + 1, nu, k);
        for (int i = 0; i < na; i++) used[added[i]] = 0;
    }
}

int main(int argc, char **argv) {
    N = atoi(argv[1]);
    if (argc > 2) MUT = 1;
    if (N < 1 || N > MAXN) return 1;
    int start = idx(0, 0);
    used[start] = 1;
    int un[1] = {start};
    redel(0, un, 1);
    fprintf(stderr, "n=%d free=%lld tiling=%lld%s\n", N, nfree, ntile, MUT ? " (mutant: translations only)" : "");
    printf("SUMMARY n=%d free=%lld tiling=%lld\n", N, nfree, ntile);
    return 0;
}
