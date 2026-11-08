/* For each prime p <= X print p and all n in [2, p-1] with n! = 1 (mod p);
   flag n with n! = 1 (mod p^2) by a trailing '*'. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  long X = atol(argv[1]);
  char *comp = calloc(X + 1, 1);
  for (long i = 2; i * i <= X; i++) if (!comp[i]) for (long j = i * i; j <= X; j += i) comp[j] = 1;
  for (long p = 3; p <= X; p++) {
    if (comp[p]) continue;
    unsigned __int128 P2 = (unsigned __int128)p * p;
    uint64_t f2 = 1;
    printf("%ld:", p);
    for (long n = 2; n < p; n++) {
      f2 = (uint64_t)(((unsigned __int128)f2 * n) % P2);
      if (f2 % p == 1) printf(" %ld%s", n, (f2 == 1) ? "*" : "");
    }
    printf("\n");
  }
  return 0;
}
