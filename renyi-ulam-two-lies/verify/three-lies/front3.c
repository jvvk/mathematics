/* Exact frontiers for the 3-lie Renyi-Ulam game, and an exhaustive check of the halving conjecture by depth.
   F[n][a][b] = largest c with (a, b, c, 0) winnable in n questions (-1 if none).
   Padding (valid for every e): (p, q, r, s) is n-winnable  <=>  r <= F[n][p][q] and V_n(p, q, r, s) <= 2^n.
   Transition: (a, b, c, 0) is n-winnable (a+b+c >= 2) iff some question (u, v, w, 0) leaves both children
     Y = (u, v + a - u, w + b - v, c - w),  N = (a - u, b - v + u, c - w + v, w)
   (n-1)-winnable.  The question's last coordinate is 0 because the last class is empty.
   Halving check (by padding it suffices to take parents (2a, 2b, 2c, 0)): for every n and a, b with
   c = floor(F[n+1][2a][2b] / 2) >= 0, the child (a, a+b, b+c, c) must be n-winnable, i.e.
   b + c <= F[n][a][a+b] (its volume is half the parent's, so the volume bound holds).
   usage: front3 NMAX            prints per depth the grid size and the number of halving violations
          front3 NMAX check a b c d n   prints whether (a,b,c,d) is n-winnable (for validation) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int64_t C_[64][64];
static int64_t W(int n, int i) { int64_t s = 0; for (int j = 0; j <= 3 - i; j++) s += C_[n][j]; return s; }
static int64_t V(int64_t a, int64_t b, int64_t c, int64_t d, int n) { return a * W(n, 0) + b * W(n, 1) + c * W(n, 2) + d; }
static int *F[64]; static int A[64], B[64]; /* F[n][a*(B[n]+1)+b], a <= A[n], b <= B[n] */
static int get(int n, int64_t a, int64_t b) {
  if (a < 0 || b < 0 || a > A[n] || b > B[n]) return -1;
  return F[n][a * (B[n] + 1) + b];
}
static int winnable(int n, int64_t p, int64_t q, int64_t r, int64_t s) {
  if (p < 0 || q < 0 || r < 0 || s < 0) return 0;
  if (p + q + r + s <= 1) return 1;
  if (n >= 0 && V(p, q, r, s, n) > ((int64_t)1 << n)) return 0;
  return r <= get(n, p, q);
}
/* is (a,b,c,0) n-winnable, n >= 1 */
static int test(int n, int a, int b, int c) {
  if (a + b + c <= 1) return 1;
  int64_t H = (int64_t)1 << (n - 1);
  if (V(a, b, c, 0, n) > 2 * H) return 0;
  for (int u = 0; u <= a; u++)
    for (int v = 0; v <= b; v++) {
      /* yes-volume = base + C(n-1,3) u + C(n-1,2) v + (n-1) w, base = a W1 + b W2 + c W3 at depth n-1 */
      int64_t base = a * W(n - 1, 1) + b * W(n - 1, 2) + (int64_t)c * W(n - 1, 3);
      int64_t lin = base + C_[n - 1][3] * u + C_[n - 1][2] * v;
      int64_t tot = V(a, b, c, 0, n);
      int64_t step = n - 1; /* coefficient of w */
      int64_t wlo = 0, whi = c;
      /* V(Y) <= H : lin + step*w <= H ; V(N) = tot - V(Y) <= H : lin + step*w >= tot - H */
      if (step == 0) { if (lin > H || lin < tot - H) continue; }
      else {
        int64_t hi = (H - lin) >= 0 ? (H - lin) / step : -1; if (hi < whi) whi = hi;
        int64_t need = tot - H - lin; int64_t lo = need <= 0 ? 0 : (need + step - 1) / step; if (lo > wlo) wlo = lo;
      }
      if (wlo > whi) continue;
      /* frontier constraints: Y = (u, v+a-u, w+b-v, c-w), N = (a-u, b-v+u, c-w+v, w) */
      int fy = get(n - 1, u, v + a - u), fn = get(n - 1, a - u, b - v + u);
      int64_t lo2 = wlo, hi2 = whi;
      /* Y third coordinate w+b-v <= fy unless Y has <= 1 element in total; handle tiny children exactly */
      for (int64_t w = lo2; w <= hi2; w++) {
        if (winnable(n - 1, u, v + a - u, w + b - v, c - w) && winnable(n - 1, a - u, b - v + u, c - w + v, w)) return 1;
        /* jump: if Y fails on its frontier, larger w only makes it worse; if N fails, try larger w */
        if (u + (v + a - u) + (w + b - v) + (c - w) > 1 && w + b - v > fy) break;
        if ((a - u) + (b - v + u) + (c - w + v) + w > 1 && c - w + v > fn) { int64_t jump = (int64_t)c + v - fn; if (jump > w) w = jump - 1; }
      }
    }
  return 0;
}
int main(int argc, char **argv) {
  for (int a = 0; a < 64; a++) for (int b = 0; b <= a; b++) C_[a][b] = (b == 0 || b == a) ? 1 : C_[a - 1][b - 1] + C_[a - 1][b];
  int NMAX = atoi(argv[1]);
  long total_viol = 0;
  /* depth 0: (a,b,c,0) winnable iff a+b+c <= 1 */
  A[0] = 1; B[0] = 1; F[0] = malloc(sizeof(int) * 4);
  for (int a = 0; a <= 1; a++) for (int b = 0; b <= 1; b++) F[0][a * 2 + b] = (a + b == 0) ? 1 : (a + b == 1 ? 0 : -1);
  for (int n = 1; n <= NMAX; n++) {
    int64_t P = (int64_t)1 << n;
    A[n] = (int)(P / W(n, 0)) + 1; B[n] = (int)(P / W(n, 1)) + 1;
    F[n] = malloc(sizeof(int) * (size_t)(A[n] + 1) * (B[n] + 1));
    for (int a = 0; a <= A[n]; a++) for (int b = 0; b <= B[n]; b++) {
      int lo = -1, hi = (int)((P - a * W(n, 0) - b * W(n, 1)) / (W(n, 2) > 0 ? W(n, 2) : 1));
      if (V(a, b, 0, 0, n) > P && a + b > 1) { F[n][a * (B[n] + 1) + b] = -1; continue; }
      if (hi < 0) hi = 0; hi += 1;
      /* monotone in c: binary search largest winnable c in [0, hi] */
      if (!test(n, a, b, 0)) { F[n][a * (B[n] + 1) + b] = -1; continue; }
      lo = 0;
      while (hi - lo > 1) { int mid = (lo + hi) / 2; if (test(n, a, b, mid)) lo = mid; else hi = mid; }
      if (test(n, a, b, hi)) lo = hi;
      F[n][a * (B[n] + 1) + b] = lo;
    }
    if (argc > 2) continue;
    /* halving check at parent depth n, child depth n-1 */
    long viol = 0, checked = 0;
    for (int a = 0; 2 * a <= A[n]; a++) for (int b = 0; 2 * b <= B[n]; b++) {
      int fp = get(n, 2 * a, 2 * b); if (fp < 0) continue;
      int c = fp / 2; checked++;
      if (2 * a + 2 * b + 2 * c <= 1) continue;
      if (!winnable(n - 1, a, a + b, b + c, c)) { viol++; if (viol <= 5) printf("  VIOLATION n=%d parent (%d,%d,%d,0) child (%d,%d,%d,%d)\n", n, 2 * a, 2 * b, 2 * c, a, a + b, b + c, c); }
    }
    total_viol += viol;
    printf("n=%2d grid %d x %d  parents checked %ld  violations %ld\n", n, A[n] + 1, B[n] + 1, checked, viol); fflush(stdout);
  }
  if (argc > 2 && !strcmp(argv[2], "check")) {
    int a = atoi(argv[3]), b = atoi(argv[4]), c = atoi(argv[5]), d = atoi(argv[6]), n = atoi(argv[7]);
    printf("%d\n", winnable(n, a, b, c, d));
  }
  return total_viol != 0; /* nonzero exit if the halving check found any violation */
}
