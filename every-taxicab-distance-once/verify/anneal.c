/* Heuristic search for perfect taxicab placements (q/4967838). Cost = number of distance values in 1..N not realised
   (equivalently collisions + overflow). Moves: shift one point by a random vector, or teleport it. Simulated annealing
   with restarts. Usage: anneal n seconds seed. Prints the first solution found, verified. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int n, N, X[64], Y[64], cnt[4096];
static unsigned long long s = 1;
static unsigned long long rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int D(int i, int j) { return abs(X[i] - X[j]) + abs(Y[i] - Y[j]); }
static int cost(void) { int c = 0; for (int d = 1; d <= N; d++) if (cnt[d] == 0) c++; return c; }
static int bump(int d, int s_) { if (d > N) return 0; cnt[d] += s_; return 1; }
int main(int argc, char **argv) {
    n = atoi(argv[1]); N = n * (n - 1) / 2; double secs = atof(argv[2]); s = argc > 3 ? atoll(argv[3]) : 1;
    int R = N / 2 + 1;
    clock_t t0 = clock();
    long long restarts = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        restarts++;
        memset(cnt, 0, sizeof cnt);
        for (int i = 0; i < n; i++) { X[i] = (int)(rnd() % (2 * R + 1)) - R; Y[i] = (int)(rnd() % (2 * R + 1)) - R; }
        int over = 0;
        for (int i = 0; i < n; i++) for (int j = 0; j < i; j++) { int d = D(i, j); if (d <= N) cnt[d]++; else over++; }
        int c = cost() + over;
        double T = 2.0;
        for (long long it = 0; it < 4000000 && c > 0; it++) {
            int i = rnd() % n, ox = X[i], oy = Y[i];
            int nx, ny;
            if (urand() < 0.8) { int step = 1 + rnd() % 4; nx = ox + (int)(rnd() % (2 * step + 1)) - step; ny = oy + (int)(rnd() % (2 * step + 1)) - step; }
            else { nx = (int)(rnd() % (2 * R + 1)) - R; ny = (int)(rnd() % (2 * R + 1)) - R; }
            int dover = 0;
            for (int j = 0; j < n; j++) if (j != i) { int d = D(i, j); if (d <= N) cnt[d]--; else dover--; }
            X[i] = nx; Y[i] = ny;
            int bad = 0;
            for (int j = 0; j < n; j++) if (j != i) { int d = D(i, j); if (d == 0) bad = 1; if (d <= N && d > 0) cnt[d]++; else dover++; }
            int c2 = bad ? 1 << 20 : cost() + over + dover;
            if (!bad && (c2 <= c || urand() < exp((c - c2) / T))) { c = c2; over += dover; }
            else {
                for (int j = 0; j < n; j++) if (j != i) { int d = D(i, j); if (d <= N && d > 0) cnt[d]--; }
                X[i] = ox; Y[i] = oy;
                for (int j = 0; j < n; j++) if (j != i) { int d = D(i, j); if (d <= N) cnt[d]++; }
            }
            T = fmax(0.05, T * 0.999999);
        }
        if (c == 0) {
            /* verify from scratch */
            int seen[4096] = {0}, okv = 1;
            for (int i = 0; i < n; i++) for (int j = 0; j < i; j++) { int d = D(i, j); if (d < 1 || d > N || seen[d]++) okv = 0; }
            printf("n=%d FOUND (verified %d) after %lld restarts, %.1fs:", n, okv, restarts, (double)(clock() - t0) / CLOCKS_PER_SEC);
            for (int i = 0; i < n; i++) printf(" (%d,%d)", X[i], Y[i]);
            printf("\n");
            return 0;
        }
    }
    printf("n=%d: none found in %.0fs (%lld restarts)\n", n, secs, restarts);
    return 1;
}
