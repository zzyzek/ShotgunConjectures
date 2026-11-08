/* a = b = 2 case of K = 3 case A: integers 2 <= u < v (not only primes) with
   (v-1) + ... check: m = p+2 with (p+2) f(u) f(v) = p u^2 v^2 + 2, f(x) = x^2 - x + 1,
   i.e. D = u^2 v^2 - f(u) f(v) divides 2(u^2 v^2 - 1). Uses the reduction v < 2u^1.5 + 2. */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
int main(int argc, char **argv) {
  long U = atol(argv[1]); long cnt = 0;
  for (long u = 2; u <= U; u++) {
    long vmax = (long)(2.0*u*__builtin_sqrt((double)u)) + 3;
    for (long v = u + 1; v <= vmax; v++) {
      u128 B = (u128)u*u*v*v;
      u128 C = (u128)(u*u - u + 1)*(v*v - v + 1);
      u128 D = B - C, N = 2*(B - 1);
      if (N % D == 0) { long m = (long)(N/D); cnt++; if (cnt < 60) printf("u=%ld v=%ld m=%ld p=%ld\n", u, v, m, m - 2); }
    }
  }
  printf("total %ld\n", cnt); return 0;
}
