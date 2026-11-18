/* Finch rule (A): x_1..x_{k-1}=0, x_k=1, x_n = x_{n-1} + [x_{n-k} != 0] (mod 3).
   For k = 2,3 mod 4: run the sequence until the capture point z (first run of zeros spaced exactly 4
   apart, G = ceil((k-1)/4) gaps, first zero r >= k+1), or until LIMIT steps. Report z, mu (last n with
   x_n != x_{n-4}, minus 4; checked to z + 4k), and x at s-5..s (s = z - 4G).
   Exits 1 if some k >= 3 has z - mu != 6 or the tail after z is not 4-periodic; k = 2 must give z = 9,
   mu = 0. A k with no capture by LIMIT is reported as a cutoff, not as a verification; exit 2 if nothing
   was verified.
   usage: capture kmin kmax limit */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int kmin = atoi(argv[1]), kmax = atoi(argv[2]);
  long long limit = atoll(argv[3]);
  int bad = 0, ok = 0, cut = 0;
  for (int k = kmin; k <= kmax; k++) {
    if (k % 4 != 2 && k % 4 != 3) continue;
    int G = (k - 1 + 3) / 4;
    long long M = 1 << 22;                 /* ring buffer (power of two > 8k) */
    unsigned char *x = calloc(M, 1);
    long long lastz = -1; int gaps = 0;
    long long lastmis = 0, z = -1;
    #define X(i) x[(i) & (M - 1)]
    for (long long n = 1; n <= limit; n++) {
      unsigned char v;
      if (n < k) v = 0; else if (n == k) v = 1;
      else { v = X(n - 1) + (X(n - k) != 0); if (v >= 3) v -= 3; }
      X(n) = v;
      if (n > 4 && v != X(n - 4)) lastmis = n;
      if (v == 0 && n >= k + 1) {
        if (lastz >= 0 && n - lastz == 4) { gaps++; }
        else { gaps = 0; }
        lastz = n;
        if (gaps == G && z < 0) {
          z = n;
          long long s = z - 4LL * G;
          printf("k=%d G=%d z=%lld s=%lld s-k=%lld x[s-5..s]=", k, G, z, s, s - k);
          for (long long i = s - 5; i <= s; i++) printf("%d", i >= 1 ? X(i) : 9);
          /* continue 4k more steps to confirm period 4 */
          long long end = n + 8LL * k;
          int tail = 1;
          for (long long m = n + 1; m <= end; m++) {
            unsigned char w = X(m - 1) + (X(m - k) != 0); if (w >= 3) w -= 3;
            X(m) = w; if (w != X(m - 4)) { lastmis = m; tail = 0; }
          }
          long long mu = lastmis >= 5 ? lastmis - 4 : 0;
          int good = tail && (k == 2 ? (z == 9 && mu == 0) : (z - mu == 6));
          printf(" mu=%lld z-mu=%lld %s\n", mu, z - mu, good ? "OK" : "FAIL");
          if (good) ok++; else bad++;
          break;
        }
      }
    }
    if (z < 0) { printf("k=%d no capture by %lld (cutoff, not verified)\n", k, limit); cut++; }
    free(x);
  }
  printf("verified %d, failed %d, cutoff %d\n", ok, bad, cut);
  return bad ? 1 : (ok == 0 ? 2 : 0);  /* 2: nothing verified (all cutoffs) */
}
