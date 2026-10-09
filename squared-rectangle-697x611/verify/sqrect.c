/* Every squared rectangle with k squares (simple or compound) from Smith networks with k+1 edges.

   Brooks-Smith-Stone-Tutte: a rectangle tiled by k squares gives a 2-connected plane multigraph G with k+1 edges
   (vertices = maximal horizontal segments, edges = squares, plus the pole edge); with unit resistors and a battery
   on the pole edge, currents = square sides, potential drop = height. Conversely any (G, pole) with every current
   nonzero is a squared rectangle. So enumerating all 2-connected plane multigraphs with <= K+1 edges and every pole
   edge finds every squared rectangle with <= K squares (over-generation is harmless for impossibility claims).

   2-connected plane multigraphs with e edges = one colour class of the simple quadrangulations with e faces
   (plantri -qc2m2, e + 2 vertices); the other class is the dual (the same tiling rotated), so one class suffices.

   Input: plantri planar_code on stdin. For each (G, pole): exact integer currents (double solve, rounded with the
   spanning-tree count D, verified exactly by L N = D b), reduced shape (W, H) with gcd of the square sides 1.
   Output: best[W][H] = fewest squares for reduced shape W x H (W, H <= LIM), dumped at the end, and a line for
   every tiling whose reduced shape is 697 x 611 or 1394 x 1222 (either orientation).
   Usage: plantri -qc2m2 NV | sqrect OUTFILE */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXV 64
#define MAXE 64
#define LIM 1500

static unsigned char best[LIM + 1][LIM + 1]; /* 0 = none */
static long long ngraphs = 0, ntilings = 0, nfail = 0;

static long long gcdll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void report(int k, long long W, long long H, int nA, int ne, int (*E)[2], int pole, const long long *N) {
    long long a = W < H ? W : H, b = W < H ? H : W;
    if ((a == 611 && b == 697) || (a == 1222 && b == 1394)) {
        printf("HIT k=%d %lldx%lld  G: nv=%d ne=%d edges:", k, W, H, nA, ne);
        for (int i = 0; i < ne; i++) printf(" %d-%d%s", E[i][0], E[i][1], i == pole ? "*" : "");
        printf("  potentials:");
        for (int v = 0; v < nA; v++) printf(" %lld", N[v]);
        printf("\n");
        fflush(stdout);
    }
}

static void solve_graph(int nA, int ne, int (*E)[2]) {
    int k = ne - 1;
    for (int p = 0; p < ne; p++) {
        int s = E[p][0], t = E[p][1];
        if (s == t) continue;
        /* reduced Laplacian of G - p, ground t: unknowns = vertices != t */
        int idx[MAXV], m = 0;
        for (int v = 0; v < nA; v++) idx[v] = (v == t) ? -1 : m++;
        double A[MAXV][MAXV + 1];
        long long Li[MAXV][MAXV];
        memset(Li, 0, sizeof Li);
        for (int i = 0; i < ne; i++) {
            if (i == p) continue;
            int u = E[i][0], v = E[i][1];
            if (u == v) continue;
            Li[u][u]++, Li[v][v]++, Li[u][v]--, Li[v][u]--;
        }
        for (int i = 0; i < nA; i++) {
            if (idx[i] < 0) continue;
            for (int j = 0; j < nA; j++)
                if (idx[j] >= 0) A[idx[i]][idx[j]] = (double)Li[i][j];
            A[idx[i]][m] = (i == s) ? 1.0 : 0.0;
        }
        /* Gaussian elimination with partial pivoting; det for D */
        double det = 1;
        int singular = 0;
        for (int c = 0; c < m; c++) {
            int piv = c;
            for (int r = c + 1; r < m; r++)
                if (fabs(A[r][c]) > fabs(A[piv][c])) piv = r;
            if (fabs(A[piv][c]) < 1e-12) {
                singular = 1;
                break;
            }
            if (piv != c) {
                for (int j = 0; j <= m; j++) {
                    double h = A[c][j];
                    A[c][j] = A[piv][j];
                    A[piv][j] = h;
                }
                det = -det;
            }
            det *= A[c][c];
            for (int r = c + 1; r < m; r++) {
                double f = A[r][c] / A[c][c];
                if (f != 0)
                    for (int j = c; j <= m; j++) A[r][j] -= f * A[c][j];
            }
        }
        if (singular) continue; /* G - p disconnected: not a squared rectangle */
        double x[MAXV];
        for (int r = m - 1; r >= 0; r--) {
            double acc = A[r][m];
            for (int j = r + 1; j < m; j++) acc -= A[r][j] * x[j];
            x[r] = acc / A[r][r];
        }
        long long D = llround(fabs(det));
        long long N[MAXV];
        for (int v = 0; v < nA; v++) N[v] = idx[v] < 0 ? 0 : llround(x[idx[v]] * (double)D);
        /* exact check: L N = D (e_s) on all non-ground rows, and total current out of s = D */
        int ok = 1;
        for (int i = 0; i < nA && ok; i++) {
            if (i == t) continue;
            long long acc = 0;
            for (int j = 0; j < nA; j++) acc += Li[i][j] * N[j];
            if (acc != (i == s ? D : 0)) ok = 0;
        }
        if (!ok) {
            nfail++;
            continue;
        }
        long long g = 0;
        int zero = 0;
        for (int i = 0; i < ne; i++) {
            if (i == p) continue;
            long long c = N[E[i][0]] - N[E[i][1]];
            if (c == 0) {
                zero = 1;
                break;
            }
            g = gcdll(g, c);
        }
        if (zero) continue;
        long long W = D / g, H = N[s] / g; /* width = total current, height = potential drop */
        if (H < 0) H = -H;
        ntilings++;
        if (W <= LIM && H <= LIM) {
            long long a = W < H ? W : H, b = W < H ? H : W;
            if (!best[a][b] || best[a][b] > k) best[a][b] = (unsigned char)k;
        }
        report(k, W, H, nA, ne, E, p, N);
    }
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: plantri -qc2m2 NV | %s OUTFILE\n", argv[0]);
        return 1;
    }
    char hdr[15];
    if (fread(hdr, 1, 15, stdin) != 15 || memcmp(hdr, ">>planar_code<<", 15)) {
        fprintf(stderr, "expected planar_code header\n");
        return 1;
    }
    int n;
    static int adj[MAXV][MAXV], deg[MAXV];
    while ((n = getchar()) != EOF) {
        for (int v = 0; v < n; v++) {
            deg[v] = 0;
            int w;
            while ((w = getchar()) != 0) adj[v][deg[v]++] = w - 1;
        }
        ngraphs++;
        /* 2-colour */
        int col[MAXV], q[MAXV], qh = 0, qt = 0;
        for (int v = 0; v < n; v++) col[v] = -1;
        col[0] = 0;
        q[qt++] = 0;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) col[w] = 1 - col[u], q[qt++] = w;
            }
        }
        int cnt0 = 0;
        for (int v = 0; v < n; v++) cnt0 += col[v] == 0;
        int cls = (cnt0 <= n - cnt0) ? 0 : 1; /* smaller class = vertices of G */
        int gid[MAXV], nA = 0;
        for (int v = 0; v < n; v++) gid[v] = col[v] == cls ? nA++ : -1;
        /* faces: dart u->v, next dart v->w with w the neighbour of v before u in v's clockwise list */
        static unsigned char seen[MAXV][MAXV];
        for (int v = 0; v < n; v++) memset(seen[v], 0, deg[v]);
        int E[MAXE][2], ne = 0;
        for (int u = 0; u < n; u++)
            for (int i = 0; i < deg[u]; i++) {
                if (seen[u][i]) continue;
                int fv[8], len = 0, cu = u, ci = i;
                while (!seen[cu][ci]) {
                    seen[cu][ci] = 1;
                    if (len < 8) fv[len] = cu;
                    len++;
                    int v = adj[cu][ci], j;
                    for (j = 0; j < deg[v]; j++)
                        if (adj[v][j] == cu) break;
                    int nj = (j - 1 + deg[v]) % deg[v];
                    cu = v;
                    ci = nj;
                }
                if (len != 4) {
                    fprintf(stderr, "non-quadrangular face\n");
                    return 2;
                }
                int a[2], na = 0;
                for (int z = 0; z < 4; z++)
                    if (gid[fv[z]] >= 0) a[na++] = gid[fv[z]];
                E[ne][0] = a[0], E[ne][1] = a[1], ne++;
            }
#ifdef MUTANT /* drop every network with parallel edges: must break agreement with A219158 */
        int par = 0;
        for (int i = 0; i < ne && !par; i++)
            for (int j = i + 1; j < ne; j++)
                if ((E[i][0] == E[j][0] && E[i][1] == E[j][1]) || (E[i][0] == E[j][1] && E[i][1] == E[j][0])) par = 1;
        if (par) continue;
#endif
        solve_graph(nA, ne, E);
    }
    FILE *f = fopen(argv[1], "w");
    for (int a = 1; a <= LIM; a++)
        for (int b = a; b <= LIM; b++)
            if (best[a][b]) fprintf(f, "%d %d %d\n", a, b, best[a][b]);
    fclose(f);
    fprintf(stderr, "graphs=%lld tilings=%lld exact-check-failures=%lld\n", ngraphs, ntilings, nfail);
    return 0;
}
