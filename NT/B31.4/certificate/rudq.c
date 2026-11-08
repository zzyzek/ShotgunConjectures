// Search n in [1,N] with n!(n+q)! | (2n-p)!  (Ruderman).
// Usage: rudq p N : for each n, largest q with n!(n+q)! | (2n-p)!; prints best q witnesses.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
static uint32_t *lpf;
static int *primes; static int np;
static long long val(long long a, long long l) {
  long long s = 0;
  while (a) { a /= l; s += a; }
  return s;
}
static int okprime(long long n, long long p, long long q, long long l) {
  return ( val(2*n-p, l) >= (val(n, l) + val(n+q, l)) );
}

static int works(long long n, long long p, long long q) {
  long long half = (p + 1) / 2;
  double rt = sqrt(2.0 * n - p);
  for (long long j = 0; j < half; j++) {
    if ((n - j) >= 2 && lpf[n - j] > rt && lpf[n - j] > p + q) { return 0; }
  }
  for (int i = 0; i < np && primes[i] <= 2 * n; i++) {
    if (!okprime(n, p, q, primes[i])) { return 0; }
  }
  // Large prime factors of n-j, and primes dividing n+q-i (wrap case) when small vs p+2q.
  //
  for (long long j = 0; j < half; j++) {
    long long m = n - j;
    while (m > 1) { long long l = lpf[m]; if (!okprime(n, p, q, l)) { return 0; } while (m % l == 0) { m /= l; } }
  }
  return 1;
}
int main(int argc, char **argv) {
  long long p = atoll(argv[1]), N = atoll(argv[2]), QMAX = 200;
  long long M = N + QMAX + 1;
  lpf = calloc(M + 1, sizeof(uint32_t));
  for (long long i = 2; i <= M; i++) {
    if (lpf[i] == 0) { for (long long j = i; j <= M; j += i) { lpf[j] = (uint32_t)i; } }
  }
  long long lim = (long long)sqrt(2.0 * N) + 2;
  if (lim < p + 2 * QMAX + 2) { lim = p + 2 * QMAX + 2; }
  primes = malloc(sizeof(int) * (lim + 1)); np = 0;
  for (long long i = 2; i <= lim; i++) { if (lpf[i] == i) { primes[np++] = (int)i; } }
  long long best = -1;
  for (long long n = (p + 2); n <= N; n++) {
    if (!works(n, p, 0)) { continue; }
    long long q = 0;
    while (q + 1 <= QMAX && works(n, p, q + 1)) { q++; }
    if (q > best) { best = q; printf("p=%lld q=%lld n=%lld\n", p, q, n); fflush(stdout); }
  }
  printf("p=%lld N=%lld bestq=%lld\n", p, N, best);
  return 0;
}
