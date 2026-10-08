// One-sided Gale-Ryser failure probability for two independent uniform compositions of n:
// P( rows(alpha) not dominated by delta^t ). alpha = ascending runs of S, delta = descending
// runs of T. Under the dominance-interval criterion (verified n<=20) failure of (S,T) is the
// union of this event and its mirror; the necessary direction is proved in Lean.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <cmath>
using namespace std;
typedef long double ld;
int n;
vector<vector<int>> P, Q; vector<ld> W;
vector<int> cur;
ld lfact[400];
void emit() {
  // weight: (#parts)! / prod m_i! / 2^(n-1)
  int r = cur.size(); ld lw = lfact[r];
  for (int i = 0; i < r;) { int j = i; while (j < r && cur[j] == cur[i]) j++; lw -= lfact[j - i]; i = j; }
  lw -= (n - 1) * logl(2.0L);
  vector<int> p(n + 1, 0), q(n + 1, 0);
  for (int k = 1; k <= n; k++) {
    p[k] = p[k - 1] + (k - 1 < r ? cur[k - 1] : 0);
    int s = 0; for (int x : cur) s += (x < k ? x : k); q[k] = s;
  }
  P.push_back(p); Q.push_back(q); W.push_back(expl(lw));
}
void gen(int rem, int mx) {
  if (rem == 0) { emit(); return; }
  for (int x = (rem < mx ? rem : mx); x >= 1; x--) { cur.push_back(x); gen(rem - x, x); cur.pop_back(); }
}
int main(int argc, char** argv) {
  n = atoi(argv[1]);
  lfact[0] = 0; for (int i = 1; i < 400; i++) lfact[i] = lfact[i - 1] + logl((ld)i);
  gen(n, n);
  size_t m = P.size(); ld fail = 0, wsum = 0;
  for (size_t a = 0; a < m; a++) {
    wsum += W[a];
    for (size_t b = 0; b < m; b++) {
      const int* pa = P[a].data(); const int* qb = Q[b].data();
      for (int k = 1; k <= n; k++) if (pa[k] > qb[k]) { fail += W[a] * W[b]; break; }
    }
  }
  printf("%d %zu %.12Le %.12Le\n", n, m, fail, wsum);
}
