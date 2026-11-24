/* Exact worst-case Renyi-Ulam liar game, e <= 3 lies. solvable(x, n) with memo.
   usage: liar E N            -> complete halving search over all halving children s with |s| <= N
          liar E check x0 .. xE  -> print q(x) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int E;
static int64_t C_[64][64];
static int64_t W(int n, int i) { int64_t s = 0; for (int j = 0; j <= E - i; j++) s += C_[n][j]; return s; } /* weight of class i with n left */
static int64_t vol(const int *x, int n) { int64_t v = 0; for (int i = 0; i <= E; i++) v += (int64_t)x[i] * W(n, i); return v; }
/* memo: open addressing, key = packed state + n */
#define TB 26
static uint64_t *keys; static uint8_t *vals;
static uint64_t pack(const int *x, int n) { uint64_t k = n; for (int i = 0; i <= E; i++) k = (k << 12) | (uint64_t)x[i]; return k + 1; }
static int look(uint64_t k) { uint64_t h = (k * 0x9E3779B97F4A7C15ULL) >> (64 - TB); while (keys[h]) { if (keys[h] == k) return vals[h]; h = (h + 1) & ((1ULL << TB) - 1); } return -1; }
static uint64_t used = 0;
static void store(uint64_t k, int v) { uint64_t h = (k * 0x9E3779B97F4A7C15ULL) >> (64 - TB); while (keys[h] && keys[h] != k) h = (h + 1) & ((1ULL << TB) - 1); if (!keys[h]) used++; keys[h] = k; vals[h] = (uint8_t)v;
  if (used > (1ULL << TB) * 7 / 10) { fprintf(stderr, "memo full\n"); exit(3); } }
static void child(const int *x, const int *q, int *y) { for (int i = 0; i <= E; i++) y[i] = q[i] + (i ? x[i - 1] - q[i - 1] : 0); }
static int solvable(const int *x, int n);
static int tryq(const int *x, int n, int *q, int i, int64_t partial, int64_t base, int64_t half, int64_t V) {
  /* yes-volume = base + sum_i q_i * c_i, c_i = W(n-1,i) - W(n-1,i+1) = C(n-1, E-i); c_E = 1 */
  if (i == E) {
    int64_t lo = V - half - base - partial, hi = half - base - partial; /* need yv <= half and V - yv <= half */
    int a = lo > 0 ? (int)lo : 0, b = hi < x[E] ? (int)hi : x[E];
    for (int t = a; t <= b; t++) {
      q[E] = t; int nq[4], y[4], z[4]; for (int k = 0; k <= E; k++) nq[k] = x[k] - q[k];
      child(x, q, y); child(x, nq, z);
      if (solvable(y, n - 1) && solvable(z, n - 1)) return 1;
    }
    return 0;
  }
  int64_t c = C_[n - 1][E - i];
  for (int t = 0; t <= x[i]; t++) { q[i] = t; if (tryq(x, n, q, i + 1, partial + c * t, base, half, V)) return 1; }
  return 0;
}
static int solvable(const int *x, int n) {
  int s = 0; for (int i = 0; i <= E; i++) s += x[i];
  if (s <= 1) return 1;
  if (n == 0) return 0;
  int64_t V = vol(x, n); if (n < 62 && V > ((int64_t)1 << n)) return 0;
  uint64_t k = pack(x, n); int m = look(k); if (m >= 0) return m;
  int64_t half = (int64_t)1 << (n - 1), base = 0; for (int i = 0; i < E; i++) base += (int64_t)x[i] * W(n - 1, i + 1);
  int q[4]; int r = tryq(x, n, q, 0, 0, base, half, V);
  store(k, r); return r;
}
static int L(const int *x) { int n = 0; while (vol(x, n) > ((int64_t)1 << n)) n++; return n; }
static int qmin(const int *x) { int n = L(x); while (!solvable(x, n)) n++; return n; }
int main(int argc, char **argv) {
  for (int a = 0; a < 64; a++) for (int b = 0; b <= a; b++) C_[a][b] = (b == 0 || b == a) ? 1 : C_[a - 1][b - 1] + C_[a - 1][b];
  E = atoi(argv[1]); keys = calloc(1ULL << TB, 8); vals = calloc(1ULL << TB, 1);
  if (argc > 2 && !strcmp(argv[2], "front")) { /* liar 2 front n : B_n(a) for a = 0.. until infeasible (e = 2 only) */
    int n = atoi(argv[3]);
    for (int a = 0;; a++) {
      int x[4] = {a, 0, 0, 0};
      if (!solvable(x, n)) { printf("\n"); break; }
      int lo = 0, hi = 1; x[1] = hi; while (solvable(x, n)) { lo = hi; hi *= 2; x[1] = hi; }
      while (hi - lo > 1) { int mid = (lo + hi) / 2; x[1] = mid; if (solvable(x, n)) lo = mid; else hi = mid; }
      printf("%d ", lo); fflush(stdout);
    }
    return 0;
  }
  if (argc > 2 && !strcmp(argv[2], "check")) { int x[4] = {0}; for (int i = 0; i <= E; i++) x[i] = atoi(argv[3 + i]); printf("%d\n", qmin(x)); return 0; }
  int N = atoi(argv[2]); long exc = 0, cex = 0;
  int s[4];
  for (int tot = 2; tot <= N; tot++) {
    /* enumerate compositions of tot into E+1 parts */
    int a, b, c;
    for (a = 0; a <= tot; a++) for (b = 0; b <= (E >= 2 ? tot - a : 0); b++) for (c = 0; c <= (E >= 3 ? tot - a - b : 0); c++) {
      if (E == 1) { s[0] = a; s[1] = tot - a; }
      else if (E == 2) { s[0] = a; s[1] = b; s[2] = tot - a - b; }
      else { s[0] = a; s[1] = b; s[2] = c; s[3] = tot - a - b - c; }
      if (E == 1 && b > 0) continue;
      if (E == 2 && c > 0) continue;
      int m = L(s); if (solvable(s, m)) continue;
      exc++; int qs = qmin(s);
      int x[4], prev = 0, ok = 1, sx = 0; for (int i = 0; i <= E; i++) { x[i] = 2 * s[i] - prev; prev = x[i]; if (x[i] < 0) ok = 0; sx += x[i]; }
      if (!ok || sx <= 1) continue;
      if (x[0] >= 4096 || x[E] >= 4096) continue;
      if (solvable(x, qs)) { cex++; printf("COUNTEREXAMPLE x=(%d,%d,%d,%d) s=(%d,%d,%d,%d) q(s)=%d x solvable in %d\n", x[0], x[1], E > 1 ? x[2] : 0, E > 2 ? x[3] : 0, s[0], s[1], E > 1 ? s[2] : 0, E > 2 ? s[3] : 0, qs, qs); fflush(stdout); }
    }
    if (tot % 20 == 0) { printf("size %d: exceptional %ld, counterexamples %ld, memo %llu\n", tot, exc, cex, (unsigned long long)used); fflush(stdout); }
  }
  printf("DONE E=%d N=%d exceptional %ld counterexamples %ld\n", E, N, exc, cex);
  return 0;
}
