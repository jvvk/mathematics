/* Inverse pairs (MSE 5146740): for primes p near the given starting points, print
   S(p) = sum_{a=1}^{p-1} 1/sqrt(a * abar)   (abar = a^{-1} mod p, by the extended Euclidean algorithm)
   C(p) = (sum_{a=1}^{p-1} 1/sqrt(a))^2 / p  (the same sum over all pairs (a, b), divided by p)
   and S(p) - 1 - C(p). Long double with Kahan summation.  Usage: sums n1 n2 ...  */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static long long inv(long long a, long long p) {
  long long t = 0, nt = 1, r = p, nr = a;
  while (nr) { long long q = r / nr, x; x = t - q * nt; t = nt; nt = x; x = r - q * nr; r = nr; nr = x; }
  return t < 0 ? t + p : t;
}
static int isprime(long long n) {
  if (n < 2) return 0;
  for (long long d = 2; d * d <= n; d++) if (n % d == 0) return 0;
  return 1;
}
int main(int argc, char **argv) {
  for (int i = 1; i < argc; i++) {
    long long p = atoll(argv[i]);
    while (!isprime(p)) p++;
    long double s = 0, cs = 0, h = 0, ch = 0;
    for (long long a = 1; a < p; a++) {
      long double y = 1.0L / sqrtl((long double)a * inv(a, p)) - cs, t = s + y;
      cs = (t - s) - y; s = t;
      long double z = 1.0L / sqrtl((long double)a) - ch, u = h + z;
      ch = (u - h) - z; h = u;
    }
    long double C = h * h / p;
    printf("p=%lld S=%.12Lf C=%.12Lf S-1-C=%+.6Le S-5=%+.6Le\n", p, s, C, s - 1 - C, s - 5);
    fflush(stdout);
  }
  return 0;
}
