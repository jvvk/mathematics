/* Good permutations (MO 514690): count every good permutation of 1..n by plain depth-first search,
   with no structural reduction. Position by position; when a_t is placed, every block ending at t
   with length 2..min(t, n-1) is tested, so a completed permutation is good.
   Usage: plain_count n  ->  "n=<n> good=<count>" and the first few permutations. */
#include <stdio.h>
#include <stdlib.h>
static int n, a[128], used[128];
static long long pre[129], cnt;
static void dfs(int t) {
  if (t > n) {
    cnt++;
    if (cnt <= 4) { for (int i = 1; i <= n; i++) printf("%d ", a[i]); printf("\n"); }
    return;
  }
  for (int v = 1; v <= n; v++) {
    if (used[v]) continue;
    pre[t] = pre[t - 1] + v;
    int ok = 1;
    for (int L = 2; L <= t && L < n && ok; L++)
      if ((pre[t] - pre[t - L]) % L == 0) ok = 0;
    if (!ok) continue;
    used[v] = 1; a[t] = v; dfs(t + 1); used[v] = 0;
  }
}
int main(int argc, char **argv) {
  n = atoi(argv[1]);
  dfs(1);
  printf("n=%d good=%lld\n", n, cnt);
  return 0;
}
