/* Checkerboard imbalance of the free hole-free n-ominoes, by Redelmeier enumeration of fixed polyominoes.
 * Independent of polys.py/parity.py. For each fixed polyomino P: hole test, imbalance c(P) = |#black - #white|,
 * stabiliser size s(P) among the 8 symmetries. A free polyomino is an orbit of 8/s fixed ones, so
 *   #free = sum s(P) / 8,   sum over free of c = sum c(P) s(P) / 8   (restricted to hole-free P).
 * Usage: ./parity n            prints n, fixed, free, free hole-free, sum c (hole-free), sum c mod 4
 * Build: cc -O2 -o parity parity.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 20
#define W (2 * MAXN + 3)
static int n;
static int cx[MAXN], cy[MAXN];
static unsigned char used[W * W];
static unsigned long long nfixed, s_all, s_hf, sc_hf, hist[MAXN + 1];

static int cmpint(const void *a, const void *b) { return (*(const int *)a > *(const int *)b) - (*(const int *)a < *(const int *)b); }

static void canon(const int *x, const int *y, int *out) {
  int mx = 1 << 30, my = 1 << 30;
  for (int i = 0; i < n; i++) { if (x[i] < mx) mx = x[i]; if (y[i] < my) my = y[i]; }
  for (int i = 0; i < n; i++) out[i] = (x[i] - mx) * 64 + (y[i] - my);
  qsort(out, n, sizeof(int), cmpint);
}

static int hole_free(void) {
  int mx = 1 << 30, my = 1 << 30, Mx = -(1 << 30), My = -(1 << 30);
  for (int i = 0; i < n; i++) {
    if (cx[i] < mx) mx = cx[i]; if (cy[i] < my) my = cy[i];
    if (cx[i] > Mx) Mx = cx[i]; if (cy[i] > My) My = cy[i];
  }
  int w = Mx - mx + 3, h = My - my + 3;
  static unsigned char g[(MAXN + 3) * (MAXN + 3)];
  static int st[(MAXN + 3) * (MAXN + 3)];
  memset(g, 0, (size_t)(w * h));
  for (int i = 0; i < n; i++) g[(cx[i] - mx + 1) * h + (cy[i] - my + 1)] = 1;
  int sp = 0, reach = 1; st[sp++] = 0; g[0] = 2;
  while (sp) {
    int v = st[--sp], a = v / h, b = v % h;
    int nb[4][2] = {{a + 1, b}, {a - 1, b}, {a, b + 1}, {a, b - 1}};
    for (int k = 0; k < 4; k++) {
      int p = nb[k][0], q = nb[k][1];
      if (p < 0 || q < 0 || p >= w || q >= h) continue;
      int id = p * h + q;
      if (g[id] == 0) { g[id] = 2; st[sp++] = id; reach++; }
    }
  }
  return reach + n == w * h;
}

static void record(void) {
  nfixed++;
  int base[MAXN], img[MAXN], tx[MAXN], ty[MAXN];
  canon(cx, cy, base);
  int s = 0;
  for (int t = 0; t < 8; t++) {
    for (int i = 0; i < n; i++) {
      int x = cx[i], y = cy[i], a, b;
      switch (t) {
        case 0: a = x; b = y; break;   case 1: a = -x; b = y; break;
        case 2: a = x; b = -y; break;  case 3: a = -x; b = -y; break;
        case 4: a = y; b = x; break;   case 5: a = -y; b = x; break;
        case 6: a = y; b = -x; break;  default: a = -y; b = -x; break;
      }
      tx[i] = a; ty[i] = b;
    }
    canon(tx, ty, img);
    if (memcmp(img, base, sizeof(int) * (size_t)n) == 0) s++;
  }
  s_all += (unsigned long long)s;
#ifdef MUT_NOSTAB
  s = 1;
#endif
#ifdef MUT_HOLES
  if (1) {
#else
  if (hole_free()) {
#endif
    int bal = 0;
#ifdef MUT_STRIPE
    for (int i = 0; i < n; i++) bal += (cx[i] & 1) ? 1 : -1;
#else
    for (int i = 0; i < n; i++) bal += ((cx[i] + cy[i]) & 1) ? 1 : -1;
#endif
    s_hf += (unsigned long long)s;
    sc_hf += (unsigned long long)(abs(bal) * s);
    hist[abs(bal)] += (unsigned long long)s;
  }
}

/* Redelmeier: cells (x, y) with y > 0, or y == 0 and x >= 0; grid offset MAXN+1 in x. */
static int ok(int x, int y) { return y > 0 || (y == 0 && x >= 0); }
#define ID(x, y) (((x) + MAXN + 1) * W + (y) + 1)

static void rec(int *untried, int nu, int depth) {
  int loc[4 * MAXN + 4];
  memcpy(loc, untried, sizeof(int) * (size_t)nu);
  while (nu > 0) {
    int c = loc[--nu];
    int x = c / W - MAXN - 1, y = c % W - 1;
    cx[depth] = x; cy[depth] = y;
    if (depth + 1 == n) { record(); continue; }
    int nw[4], k = 0;
    int nb[4][2] = {{x + 1, y}, {x - 1, y}, {x, y + 1}, {x, y - 1}};
    for (int j = 0; j < 4; j++) {
      int a = nb[j][0], b = nb[j][1];
      if (!ok(a, b) || used[ID(a, b)]) continue;
      used[ID(a, b)] = 1; nw[k++] = ID(a, b);
    }
    int next[4 * MAXN + 4];
    memcpy(next, loc, sizeof(int) * (size_t)nu);
    memcpy(next + nu, nw, sizeof(int) * (size_t)k);
    rec(next, nu + k, depth + 1);
    for (int j = 0; j < k; j++) used[nw[j]] = 0;
  }
}

int main(int argc, char **argv) {
  n = atoi(argv[1]);
  if (n < 1 || n > MAXN) return 1;
  int start = ID(0, 0);
  used[start] = 1;
  rec(&start, 1, 0);
  printf("n=%d fixed=%llu free=%llu free_holefree=%llu sum_c=%llu mod4=%llu\n", n, nfixed, s_all / 8, s_hf / 8,
         sc_hf / 8, (sc_hf / 8) % 4);
  printf("hist:");
  for (int c = 0; c <= n; c++) if (hist[c]) printf(" %d:%llu", c, hist[c] / 8);
  printf("\n");
  if (s_all % 8 || s_hf % 8 || sc_hf % 8) puts("BURNSIDE REMAINDER NONZERO");
  return 0;
}
