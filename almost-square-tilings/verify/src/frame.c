/* Frame dissections for the almost-square induction.
 *
 * Tile a W x H rectangle exactly by: one "hole" of shape m x (m+1) (either orientation), plus
 * distinct almost-squares k x (k+1), each size k in [lo, hi] used at most once, either
 * orientation. (With the hole tiled recursively by sizes < m and lo >= m, all pieces are
 * distinct.) Set m = 0 for no hole.
 *
 * Skyline search: the bottom-left cell of any well is a piece corner; MRV picks the narrowest.
 * Usage: frame W H lo hi m [maxsol]   Prints each solution as "SOL" + "k w h x y" lines
 * (k = size, w x h = placed dimensions, k = -m for the hole), then "COUNT c".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXD 1024
#define MAXP 128

static int W, H, lo, hi, m, holeleft, maxsol;
static int avail[MAXD];
static int h[MAXD];
static int pk[MAXP], pw[MAXP], ph[MAXP], px[MAXP], py[MAXP], np;
static long long nsol, nodes;

static void emit(void) {
    printf("SOL\n");
    for (int i = 0; i < np; i++) printf("%d %d %d %d %d\n", pk[i], pw[i], ph[i], px[i], py[i]);
}

static int try_place(int k, int w, int hh, int x0, int m0);

static void solve(void) {
    nodes++;
    int done = 1;
    for (int x = 0; x < W; x++) if (h[x] < H) { done = 0; break; }
    if (done) { if (!holeleft) { nsol++; emit(); } return; }
    int m0 = H + 1, x0 = 0, wd = W + 1;
    for (int x = 0; x < W;) {
        int e = x;
        while (e < W && h[e] == h[x]) e++;
        int lwall = (x == 0) || h[x - 1] > h[x];
        int rwall = (e == W) || h[e] > h[x];
        if (lwall && rwall && h[x] < H && e - x < wd) { m0 = h[x]; x0 = x; wd = e - x; }
        x = e;
    }
    /* hole */
    if (holeleft) {
        int dims[2][2] = {{m + 1, m}, {m, m + 1}};
        for (int o = 0; o < 2; o++) {
            int w = dims[o][0], hh = dims[o][1];
            if (w > wd || m0 + hh > H) continue;
            holeleft = 0;
            try_place(-m, w, hh, x0, m0);
            holeleft = 1;
            if (maxsol && nsol >= maxsol) return;
        }
    }
    for (int k = hi; k >= lo; k--) {
        if (!avail[k]) continue;
        int dims[2][2] = {{k + 1, k}, {k, k + 1}};
        for (int o = 0; o < 2; o++) {
            int w = dims[o][0], hh = dims[o][1];
            if (w > wd || m0 + hh > H) continue;
            avail[k] = 0;
            try_place(k, w, hh, x0, m0);
            avail[k] = 1;
            if (maxsol && nsol >= maxsol) return;
        }
    }
}

static int try_place(int k, int w, int hh, int x0, int m0) {
    for (int x = x0; x < x0 + w; x++) h[x] += hh;
    pk[np] = k; pw[np] = w; ph[np] = hh; px[np] = x0; py[np] = m0; np++;
    solve();
    np--;
    for (int x = x0; x < x0 + w; x++) h[x] -= hh;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: frame W H lo hi m [maxsol]\n"); return 2; }
    W = atoi(argv[1]); H = atoi(argv[2]); lo = atoi(argv[3]); hi = atoi(argv[4]); m = atoi(argv[5]);
    maxsol = argc > 6 ? atoi(argv[6]) : 0;
    if (W >= MAXD || H >= MAXD || hi >= MAXD) { fprintf(stderr, "too big\n"); return 2; }
    for (int k = lo; k <= hi; k++) avail[k] = 1;
    holeleft = m > 0;
    solve();
    printf("COUNT %lld nodes=%lld\n", nsol, nodes);
    return 0;
}
