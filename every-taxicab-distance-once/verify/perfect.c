/* MSE q/4967838: n lattice points whose C(n,2) taxicab distances are exactly 1, 2, ..., C(n,2).
   Exact search, largest distance first. P = placed points, d = largest distance not yet realised. In a solution the pair
   realising d has at least one endpoint outside P: either (1) q new, r in P, |q-r| = d, or (2) both new.
   Symmetry: p0 = (0,0), p1 = (a, N-a), 0 <= a <= N/2.
   Usage: perfect n [maxsol] [mutant]   mutant 1: skip branch (2) (incomplete search, must lose solutions).
   Prints solutions (up to 5) and the total count of (possibly symmetric) solutions found, and node count. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, N, MUT, px[40], py[40], np_, used[2000];
static long long nodes, sols, maxsol;
static int dist(int ax, int ay, int bx, int by) { return abs(ax - bx) + abs(ay - by); }
static int canadd(int x, int y, int *ds) { /* distances to P distinct, unused; return count */
    for (int i = 0; i < np_; i++) {
        int d = dist(x, y, px[i], py[i]);
        if (d == 0 || d > N || used[d]) return 0;
        for (int j = 0; j < i; j++) if (ds[j] == d) return 0;
        ds[i] = d;
    }
    return 1;
}
static void add(int x, int y, int *ds) { for (int i = 0; i < np_; i++) used[ds[i]] = 1; px[np_] = x; py[np_] = y; np_++; }
static void del(int *ds) { np_--; for (int i = 0; i < np_; i++) used[ds[i]] = 0; }
static void rec(void) {
    nodes++;
    if (np_ == n) {
        sols++;
        if (sols <= 5) { printf("solution:"); for (int i = 0; i < n; i++) printf(" (%d,%d)", px[i], py[i]); printf("\n"); }
        return;
    }
    if (maxsol && sols >= maxsol) return;
    int d = N; while (d > 0 && used[d]) d--;
    int ds[40], ds2[40];
    /* (1) q new at distance d from some placed r */
    for (int i = 0; i < np_; i++)
        for (int t = 0; t < 4 * d; t++) {
            int k = t % d, side = t / d, dx, dy;           /* walk the L1 sphere of radius d */
            if (side == 0) { dx = k; dy = d - k; } else if (side == 1) { dx = d - k; dy = -k; }
            else if (side == 2) { dx = -k; dy = -(d - k); } else { dx = -(d - k); dy = k; }
            int x = px[i] + dx, y = py[i] + dy;
            if (!canadd(x, y, ds)) continue;
            add(x, y, ds); rec(); del(ds);
            if (maxsol && sols >= maxsol) return;
        }
    /* (2) two new points q, r with |q - r| = d, every distance to P below d */
    if (MUT == 1 || np_ > n - 2) return;
    int minx = 1 << 30, maxx = -(1 << 30), miny = 1 << 30, maxy = -(1 << 30);
    for (int i = 0; i < np_; i++) { if (px[i] < minx) minx = px[i]; if (px[i] > maxx) maxx = px[i]; if (py[i] < miny) miny = py[i]; if (py[i] > maxy) maxy = py[i]; }
    for (int x = maxx - d; x <= minx + d; x++)
        for (int y = maxy - d; y <= miny + d; y++) {
            if (!canadd(x, y, ds)) continue;
            add(x, y, ds);
            if (!used[d])
                for (int t = 0; t < 4 * d; t++) {
                    int k = t % d, side = t / d, dx, dy;
                    if (side == 0) { dx = k; dy = d - k; } else if (side == 1) { dx = d - k; dy = -k; }
                    else if (side == 2) { dx = -k; dy = -(d - k); } else { dx = -(d - k); dy = k; }
                    int X = x + dx, Y = y + dy;
                    if (X < x || (X == x && Y <= y)) continue;       /* unordered pair, q < r */
                    /* r's distances to old P must be < d; to q it is d */
                    int ok = 1;
                    for (int i = 0; i < np_ - 1; i++) if (dist(X, Y, px[i], py[i]) >= d) { ok = 0; break; }
                    if (!ok || !canadd(X, Y, ds2)) continue;
                    add(X, Y, ds2); rec(); del(ds2);
                    if (maxsol && sols >= maxsol) { del(ds); return; }
                }
            del(ds);
        }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); N = n * (n - 1) / 2; maxsol = argc > 2 ? atoll(argv[2]) : 0; MUT = argc > 3 ? atoi(argv[3]) : 0;
    for (int a = 0; a <= N / 2; a++) {
        memset(used, 0, sizeof used); np_ = 0;
        px[0] = 0; py[0] = 0; np_ = 1;
        int ds[40]; ds[0] = N; used[N] = 1; px[1] = a; py[1] = N - a; np_ = 2;
        rec();
        if (maxsol && sols >= maxsol) break;
    }
    printf("n=%d N=%d: %lld solutions found (with repeats), %lld nodes\n", n, N, sols, nodes);
    return 0;
}
