/* Independent recheck (shares no code with ../parity.c): grow FREE polyominoes level by level.
 * Level k holds canonical forms (min over the 8 symmetries of the sorted, translated cell list) in an open-addressing
 * hash set; level k+1 = canonical forms of every level-k shape plus one adjacent cell. For the last level it reports
 * the number of free shapes, the number without holes (holes found by flood fill from outside the bounding box),
 * the sum of |black - white| over those, and a histogram of that imbalance.
 * Build: cc -O2 -o grow grow.c     Run: ./grow 16
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
typedef struct { uint8_t c[MAXN]; } Shape;   /* cell = 16*x + y, x,y < 16, sorted ascending */
static int N;

static int cmpu8(const void *a, const void *b) { return *(const uint8_t *)a - *(const uint8_t *)b; }

static void canonical(const int *x, const int *y, int k, Shape *out) {
  Shape best; int first = 1;
  for (int t = 0; t < 8; t++) {
    int a[MAXN], b[MAXN], mx = 99, my = 99;
    for (int i = 0; i < k; i++) {
      int p = (t & 4) ? y[i] : x[i], q = (t & 4) ? x[i] : y[i];
      if (t & 1) p = -p;
      if (t & 2) q = -q;
      a[i] = p; b[i] = q; if (p < mx) mx = p; if (q < my) my = q;
    }
    Shape s; memset(&s, 0, sizeof s);
    for (int i = 0; i < k; i++) s.c[i] = (uint8_t)(16 * (a[i] - mx) + (b[i] - my));
    qsort(s.c, (size_t)k, 1, cmpu8);
    if (first || memcmp(s.c, best.c, (size_t)k) < 0) { best = s; first = 0; }
  }
  *out = best;
}

typedef struct { Shape *tab; uint8_t *full; size_t cap, cnt; } Set;
static uint64_t hsh(const Shape *s, int k) {
  uint64_t h = 1469598103934665603ULL;
  for (int i = 0; i < k; i++) { h ^= s->c[i]; h *= 1099511628211ULL; }
  return h;
}
static void set_init(Set *S, size_t cap) {
  S->cap = cap; S->cnt = 0; S->tab = malloc(cap * sizeof(Shape)); S->full = calloc(cap, 1);
  if (!S->tab || !S->full) { fprintf(stderr, "out of memory\n"); exit(1); }
}
static void set_add(Set *S, const Shape *s, int k) {
  size_t i = hsh(s, k) % S->cap;
  while (S->full[i]) { if (memcmp(S->tab[i].c, s->c, (size_t)k) == 0) return; i = (i + 1) % S->cap; }
  S->full[i] = 1; S->tab[i] = *s; S->cnt++;
  if (S->cnt * 10 > S->cap * 7) { fprintf(stderr, "hash table too full\n"); exit(1); }
}

static int holefree(const int *x, const int *y, int k, int *bal) {
  int g[20][20]; memset(g, 0, sizeof g);
  int Mx = 0, My = 0;
  for (int i = 0; i < k; i++) { g[x[i] + 1][y[i] + 1] = 1; if (x[i] > Mx) Mx = x[i]; if (y[i] > My) My = y[i]; }
  int w = Mx + 3, h = My + 3, st[400], sp = 0, out = 1;
  g[0][0] = 2; st[sp++] = 0;
  while (sp) {
    int v = st[--sp], a = v / 20, b = v % 20;
    int d[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};
    for (int j = 0; j < 4; j++) {
      int p = a + d[j][0], q = b + d[j][1];
      if (p < 0 || q < 0 || p >= w || q >= h || g[p][q]) continue;
      g[p][q] = 2; st[sp++] = p * 20 + q; out++;
    }
  }
  int s = 0;
#ifdef MUT_STRIPE
  for (int i = 0; i < k; i++) s += (x[i] % 2) ? 1 : -1;
#else
  for (int i = 0; i < k; i++) s += ((x[i] + y[i]) % 2) ? 1 : -1;
#endif
  *bal = abs(s);
  return out + k == w * h;
}

int main(int argc, char **argv) {
  N = atoi(argv[1]);
  if (N < 1 || N > MAXN) return 1;
  /* table sizes only (an undersized table aborts; it cannot change a count): 2.2 x the free counts A000105 */
  static const double sizes[MAXN + 1] = {0, 1, 1, 2, 5, 12, 35, 108, 369, 1285, 4655, 17073, 63600, 238591, 901971,
                                         3426576, 13079255};
  size_t caps[MAXN + 1] = {0};
  for (int k = 1; k <= N; k++) caps[k] = (size_t)(sizes[k] * 2.2) + 64;
  Set cur; set_init(&cur, 64);
  Shape one; memset(&one, 0, sizeof one); set_add(&cur, &one, 1);
  for (int k = 1; k < N; k++) {
    Set nxt; set_init(&nxt, caps[k + 1]);
    for (size_t i = 0; i < cur.cap; i++) {
      if (!cur.full[i]) continue;
      int x[MAXN + 1], y[MAXN + 1];
      for (int j = 0; j < k; j++) { x[j] = cur.tab[i].c[j] / 16 + 1; y[j] = cur.tab[i].c[j] % 16 + 1; }
      for (int j = 0; j < k; j++) {
        int d[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};
        for (int e = 0; e < 4; e++) {
          int p = x[j] + d[e][0], q = y[j] + d[e][1], dup = 0;
          for (int m = 0; m < k; m++) if (x[m] == p && y[m] == q) { dup = 1; break; }
          if (dup) continue;
          x[k] = p; y[k] = q;
          Shape s; canonical(x, y, k + 1, &s); set_add(&nxt, &s, k + 1);
        }
      }
    }
    free(cur.tab); free(cur.full); cur = nxt;
  }
  unsigned long long hf = 0, sum = 0, hist[MAXN + 1] = {0};
  for (size_t i = 0; i < cur.cap; i++) {
    if (!cur.full[i]) continue;
    int x[MAXN], y[MAXN], bal;
    for (int j = 0; j < N; j++) { x[j] = cur.tab[i].c[j] / 16; y[j] = cur.tab[i].c[j] % 16; }
    if (holefree(x, y, N, &bal)) { hf++; sum += (unsigned long long)bal; hist[bal]++; }
  }
  printf("n=%d free=%zu free_holefree=%llu sum_c=%llu mod4=%llu hist:", N, cur.cnt, hf, sum, sum % 4);
  for (int c = 0; c <= N; c++) if (hist[c]) printf(" %d:%llu", c, hist[c]);
  printf("\n");
  return 0;
}
