// Exhaustive search: all n in [1, X] with sigma_inf(n) = k n (k integer).
// sigma_inf(n) = prod over prime powers p^e || n of prod over set bits i of e of (1 + p^(2^i)).
// Segmented sieve; prints every multiperfect n with k and whether 3 | n.
// Usage: isig X [segment] [start]  (prints a progress line after each segment)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128;
int main(int argc, char **argv) {
  uint64_t X = strtoull(argv[1], 0, 10);
  uint64_t S = ( argc > 2 ? strtoull(argv[2], 0, 10) : 10000000ULL );
  uint64_t START = ( argc > 3 ? strtoull(argv[3], 0, 10) : 1ULL );
  uint64_t r = (uint64_t)sqrtl((long double)X) + 2;
  char *comp = calloc(r + 1, 1);
  uint32_t *pr = malloc(sizeof(uint32_t) * (r + 1)); uint64_t np = 0;
  for (uint64_t i = 2; i <= r; i++) {
    if (!comp[i]) { pr[np++] = (uint32_t)i; for (uint64_t j = i * i; j <= r; j += i) { comp[j] = 1; } }
  }
  uint64_t *rem = malloc(sizeof(uint64_t) * S);
  u128 *sig = malloc(sizeof(u128) * S);
  uint64_t found = 0, found3 = 0;
  for (uint64_t lo = START; lo <= X; lo += S) {
    uint64_t hi = lo + S - 1; if (hi > X) { hi = X; }
    uint64_t L = hi - lo + 1;
    for (uint64_t i = 0; i < L; i++) { rem[i] = lo + i; sig[i] = 1; }
    for (uint64_t t = 0; t < np; t++) {
      uint64_t p = pr[t];
      if (p * p > hi) { break; }
      uint64_t start = ((lo + p - 1) / p) * p;
      for (uint64_t m = start; m <= hi; m += p) {
        uint64_t i = m - lo, e = 0;
        while (rem[i] % p == 0) { rem[i] /= p; e++; }
        u128 f = 1; uint64_t pw = p; int b = 0;
        while (e) {
          if (e & 1) { f *= (u128)(1 + pw); }
          e >>= 1; b++;
          if (e) { pw = pw * pw; }
        }
        sig[i] *= f;
      }
    }
    for (uint64_t i = 0; i < L; i++) {
      uint64_t n = lo + i;
      if (rem[i] > 1) { sig[i] *= (u128)(rem[i] + 1); }
      if (sig[i] % n == 0) {
        found++;
        int d3 = ( n % 3 == 0 );
        if (!d3) { found3++; }
        printf("%llu k=%llu div3=%d\n", (unsigned long long)n, (unsigned long long)(sig[i] / n), d3);
        fflush(stdout);
      }
    }
    if ( (hi % 1000000000ULL) == 0 ) { printf("done through %llu\n", (unsigned long long)hi); fflush(stdout); }
  }
  printf("START=%llu X=%llu total=%llu not_div3=%llu\n", (unsigned long long)START, (unsigned long long)X, (unsigned long long)found, (unsigned long long)found3);
  return 0;
}
