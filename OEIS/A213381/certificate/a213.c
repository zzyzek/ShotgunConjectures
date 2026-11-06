#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
/* a(n) = (-2)^n mod (n+2); report n < N with a(n) in {5,10,71,107}. */
static uint64_t pw(uint64_t b, uint64_t e, uint64_t m) {
  unsigned __int128 r = 1 % m, x = b % m;
  while (e) { if (e & 1) r = (r * x) % m; x = (x * x) % m; e >>= 1; }
  return (uint64_t)r;
}
int main(int argc, char **argv) {
  uint64_t N = strtoull(argv[1], 0, 10), n;
  for (n = 0; n < N; n++) {
    uint64_t m = n + 2, v = pw(m - 2, n, m);
    if (v == 5 || v == 10 || v == 71 || v == 107) { printf("%llu %llu\n", (unsigned long long)n, (unsigned long long)v); fflush(stdout); }
  }
  return 0;
}
