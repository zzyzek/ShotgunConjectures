/* A110073: n with sigma(n) = 2n - phi(phi(n)), n <= N.
   Print each solution not of the form 10(8p+1) with p, 8p+1 prime, and count all. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  long N = atol(argv[1]);
  uint32_t *phi = malloc((N + 1) * sizeof(uint32_t));
  uint64_t *sig = calloc(N + 1, sizeof(uint64_t));
  for (long i = 0; i <= N; i++) phi[i] = i;
  for (long p = 2; p <= N; p++) if (phi[p] == p) for (long j = p; j <= N; j += p) phi[j] -= phi[j] / p;
  for (long d = 1; d <= N; d++) for (long m = d; m <= N; m += d) sig[m] += d;
  long cnt = 0, other = 0;
  for (long n = 1; n <= N; n++) {
    if (sig[n] + phi[phi[n]] != 2 * (uint64_t)n) continue;
    cnt++;
    int fam = 0;
    if (n % 10 == 0) { long q = n / 10; if (q > 1 && phi[q] == q - 1 && (q - 1) % 8 == 0) { long p = (q - 1) / 8; if (p > 2 && phi[p] == p - 1) fam = 1; } }
    if (!fam) { other++; printf("other %ld\n", n); }
  }
  printf("N %ld solutions %ld outside family %ld\n", N, cnt, other);
  return 0;
}
