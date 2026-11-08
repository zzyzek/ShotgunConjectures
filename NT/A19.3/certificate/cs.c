// For every odd n in [lo, hi], find a representation n = p^a + 2^b, n = p^a - 2^b or
// n = 2^b - p^a with p prime, a >= 1, b >= 1 (most restrictive reading), using
// deterministic Miller-Rabin (Sinclair's 7 bases, valid for all n < 2^64) on 64-bit values.
// Prints any n with no representation using b <= 62, and summary statistics.
// Usage: cs lo hi
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128;
static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)(((u128)a * b) % m); }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
  uint64_t r = 1; a %= m;
  while (e) { if (e & 1) { r = mulmod(r, a, m); } a = mulmod(a, a, m); e >>= 1; }
  return r;
}
static const int sp[] = {3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97};
static int isprime(uint64_t n) {
  if (n < 2) { return 0; }
  if ((n % 2) == 0) { return ( n == 2 ); }
  for (int i = 0; i < 24; i++) { if ((n % sp[i]) == 0) { return ( n == (uint64_t)sp[i] ); } }
  if (n < 9409) { return 1; }
  uint64_t d = n - 1; int s = 0;
  while ((d & 1) == 0) { d >>= 1; s++; }
  static const uint64_t B[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
  for (int i = 0; i < 7; i++) {
    uint64_t a = B[i] % n;
    if (a == 0) { continue; }
    uint64_t x = powmod(a, d, n);
    if ( (x == 1) || (x == n - 1) ) { continue; }
    int ok = 0;
    for (int r = 1; r < s; r++) { x = mulmod(x, x, n); if (x == n - 1) { ok = 1; break; } }
    if (!ok) { return 0; }
  }
  return 1;
}
// Odd prime power test: n = p^a, a >= 1.
//
static int isprimepow(uint64_t n) {
  if (n < 3) { return 0; }
  if (isprime(n)) { return 1; }
  for (int a = 2; a <= 40; a++) {
    long double r = powl((long double)n, 1.0L / a);
    uint64_t c = (uint64_t)(r + 0.5L);
    for (uint64_t t = (c > 2 ? c - 1 : 2); t <= c + 1; t++) {
      u128 v = 1; int big = 0;
      for (int j = 0; j < a; j++) { v *= t; if (v > n) { big = 1; break; } }
      if ( (!big) && (v == n) && isprime(t) ) { return 1; }
    }
    if (c < 3) { break; }
  }
  return 0;
}
#include <math.h>
int main(int argc, char **argv) {
  uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
  if ((lo & 1) == 0) { lo++; }
  uint64_t maxb = 0, maxbn = 0, hard = 0, ppow = 0;
  for (uint64_t n = lo; n <= hi; n += 2) {
    int found = 0;
    for (int b = 1; b <= 62 && !found; b++) {
      uint64_t t = 1ULL << b;
      if ( (n > t) && isprime(n - t) ) { found = b; break; }
      if ( (t > n) && isprime(t - n) ) { found = b; break; }
      if ( isprime(n + t) ) { found = b; break; }
    }
    if (!found) {
      for (int b = 1; b <= 62 && !found; b++) {
        uint64_t t = 1ULL << b;
        if ( ( (n > t) && isprimepow(n - t) ) || ( (t > n) && isprimepow(t - n) ) || isprimepow(n + t) ) { found = b; ppow++; }
      }
    }
    if (!found) { hard++; printf("HARD %llu\n", (unsigned long long)n); fflush(stdout); continue; }
    if ((uint64_t)found > maxb) { maxb = found; maxbn = n; printf("record b=%d n=%llu\n", found, (unsigned long long)n); fflush(stdout); }
  }
  printf("range [%llu,%llu] hard=%llu primepow_only=%llu maxb=%llu at n=%llu\n", (unsigned long long)lo, (unsigned long long)hi,
         (unsigned long long)hard, (unsigned long long)ppow, (unsigned long long)maxb, (unsigned long long)maxbn);
  return 0;
}
