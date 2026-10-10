/* Good permutations (MO 514690): exhaustive search for n = 2^m - 1 using the reduction proved in
   Lean (GoodPerm.reduction): with q = (n+1)/2, a good permutation has a_q = q and
   {a_i, a_{i+q}} = {x, x+q} for i < q. So a_1..a_{q-1} determine the permutation. When a_t is
   placed (t < q), every block inside 1..t and every block inside q+1..q+t is tested; each completed
   candidate is then tested block by block. Compile with -DMUTANT to skip block lengths dividing n
   (a planted error that the driver must catch).
   Usage: half_search n  ->  "n=<n> good=<count> nodes=<nodes>" and the first few permutations. */
#include <stdio.h>
#include <stdlib.h>
static int n, q, a[256], used[256];
static long long pre[257], pre2[257], nodes, cnt;
static int skip(int L) {
#ifdef MUTANT
  return n % L == 0;
#else
  (void)L; return 0;
#endif
}
static int partner(int x) { return x < q ? x + q : x - q; }
static int fullcheck(void) {
  long long P[257]; P[0] = 0;
  for (int t = 1; t <= n; t++) P[t] = P[t - 1] + a[t];
  for (int L = 2; L < n; L++) {
    if (skip(L)) continue;
    for (int s = 0; s + L <= n; s++) if ((P[s + L] - P[s]) % L == 0) return 0;
  }
  return 1;
}
static void dfs(int t) {
  if (t == q) {
    a[q] = q;
    for (int i = 1; i < q; i++) a[i + q] = partner(a[i]);
    if (fullcheck()) {
      cnt++;
      if (cnt <= 4) { for (int i = 1; i <= n; i++) printf("%d ", a[i]); printf("\n"); }
    }
    return;
  }
  nodes++;
  for (int v = 1; v <= n; v++) {
    if (v == q || used[v]) continue;
    int w = partner(v);
    pre[t] = pre[t - 1] + v; pre2[t] = pre2[t - 1] + w;
    int ok = 1;
    for (int L = 2; L <= t && ok; L++) {
      if (skip(L)) continue;
      if ((pre[t] - pre[t - L]) % L == 0 || (pre2[t] - pre2[t - L]) % L == 0) ok = 0;
    }
    if (!ok) continue;
    used[v] = used[w] = 1; a[t] = v; dfs(t + 1); used[v] = used[w] = 0;
  }
}
int main(int argc, char **argv) {
  n = atoi(argv[1]); q = (n + 1) / 2;
  if (n < 3 || (q & (q - 1)) != 0) { printf("n must be 2^m - 1 >= 3\n"); return 1; }
  dfs(1);
  printf("n=%d good=%lld nodes=%lld\n", n, cnt, nodes);
  return 0;
}
