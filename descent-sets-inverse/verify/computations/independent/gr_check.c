/* Independent recheck of the Remark 3.4 rate numbers. Failure of rows(alpha) <= delta^t is
   tested in the conjugate form delta <= alpha^t (conjugation reverses dominance), for two
   independent uniform compositions alpha, delta of n. Weights: compositions per partition =
   r!/prod(mult!), probability = weight / 2^(n-1). Block mechanism: delta has a part > #parts(alpha). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#define MAXP 80000
#define MAXN 50
static int n, np, parts[MAXP][MAXN + 1], len[MAXP], cur[MAXN + 1];
static long double wt[MAXP];
static int top[MAXP][MAXN + 2], cps[MAXP][MAXN + 2];   /* prefix sums of parts; of conjugate */
static void gen(int rem, int mx, int k) {
  if (rem == 0) { for (int i = 0; i < k; i++) parts[np][i] = cur[i]; len[np] = k; np++; return; }
  for (int x = rem < mx ? rem : mx; x >= 1; x--) { cur[k] = x; gen(rem - x, x, k + 1); }
}
int main(int argc, char **argv) {
  n = atoi(argv[1]); gen(n, n, 0);
  for (int p = 0; p < np; p++) {
    int r = len[p]; long double lw = lgammal(r + 1);
    for (int i = 0; i < r;) { int j = i; while (j < r && parts[p][j] == parts[p][i]) j++; lw -= lgammal(j - i + 1); i = j; }
    wt[p] = expl(lw - (n - 1) * logl(2.0L));
    top[p][0] = 0; for (int k = 1; k <= n; k++) top[p][k] = top[p][k - 1] + (k <= r ? parts[p][k - 1] : 0);
    cps[p][0] = 0; for (int k = 1; k <= n; k++) { int c = 0; for (int i = 0; i < r; i++) if (parts[p][i] >= k) c++; cps[p][k] = cps[p][k - 1] + c; }
  }
  long double fail = 0, block = 0, tot = 0;
  for (int a = 0; a < np; a++) {             /* alpha */
    tot += wt[a];
    for (int d = 0; d < np; d++) {           /* delta: fail iff delta not <= conj(alpha) */
      int bad = 0;
      for (int k = 1; k <= n; k++) if (top[d][k] > cps[a][k]) { bad = 1; break; }
      if (bad) fail += wt[a] * wt[d];
      if (parts[d][0] > len[a]) block += wt[a] * wt[d];
    }
  }
  printf("%d %.10Le %.10Le %.6Lf %.4Lf %.6Lf\n", n, fail, block, fail / block, fail / powl(0.75L, n), tot);
  return 0;
}
