// Search n in [1,N] with n!(n+q)! | (2n-p)!  (Ruderman).
// Usage: rud p q N
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
int main(int argc, char **argv) {
  long long p = atoll(argv[1]), q = atoll(argv[2]), N = atoll(argv[3]);
  long long M = N + 1;
  lpf = calloc(M + 1, sizeof(uint32_t));
  for (long long i = 2; i <= M; i++) {
    if (lpf[i] == 0) { for (long long j = i; j <= M; j += i) { lpf[j] = (uint32_t)i; } }
  }
  long long lim = (long long)sqrt(2.0 * N) + 2;
  if (lim < p + q + 2) { lim = p + q + 2; }
  primes = malloc(sizeof(int) * (lim + 1)); np = 0;
  for (long long i = 2; i <= lim; i++) { if (lpf[i] == i) { primes[np++] = (int)i; } }
  long long cnt = 0;
  long long half = (p + 1) / 2;
  for (long long n = (p + q + 2); n <= N; n++) {
    double rt = sqrt(2.0 * n - p);
    int bad = 0;
    for (long long j = 0; j < half; j++) {
      if ((n - j) >= 2 && lpf[n - j] > rt && lpf[n - j] > p + q) { bad = 1; break; }
    }
    if (bad) { continue; }
    for (int i = 0; i < np && primes[i] <= 2 * n; i++) {
      if (!okprime(n, p, q, primes[i])) { bad = 1; break; }
    }
    if (bad) { continue; }
    // Recheck exactly the prime factors of n-j (large ones).
    for (long long j = 0; j < half && !bad; j++) {
      long long m = n - j;
      while (m > 1) { long long l = lpf[m]; if (!okprime(n, p, q, l)) { bad = 1; break; } while (m % l == 0) { m /= l; } }
    }
    if (bad) { continue; }
    cnt++;
    if (cnt <= 10) { printf("p=%lld q=%lld n=%lld\n", p, q, n); }
  }
  printf("p=%lld q=%lld N=%lld count=%lld\n", p, q, N, cnt);
  return 0;
}
