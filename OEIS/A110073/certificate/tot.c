/* Shape n = 2^a q (a >= 3, q = 2t+1 prime, t odd) of sigma(n) = 2n - phi(phi(n)) reduces to
   t + 1 = 2^(a-2) (phi(t) + 4). Search odd t <= T, all a. Also report solutions ignoring primality of 2t+1. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  long T = atol(argv[1]);
  long M = 2 * T + 2;
  uint32_t *phi = malloc((T + 1) * sizeof(uint32_t));
  for (long i = 0; i <= T; i++) phi[i] = i;
  for (long p = 2; p <= T; p++) if (phi[p] == p) for (long j = p; j <= T; j += p) phi[j] -= phi[j] / p;
  /* primality of 2t+1 by trial division only when needed */
  long hits = 0;
  for (long t = 1; t <= T; t += 2) {
    long u = t + 1; int j = 0;
    while (u % 2 == 0) { u /= 2; j++;
      if ((long)phi[t] + 4 == u) {
        long q = 2 * t + 1; int pr = 1;
        for (long d = 3; d * d <= q; d += 2) if (q % d == 0) { pr = 0; break; }
        printf("t=%ld a=%d phi=%u q=2t+1=%ld prime=%d n=2^a*q\n", t, j + 2, phi[t], q, pr);
        hits++;
      }
    }
  }
  printf("T %ld hits %ld\n", T, hits);
  (void)M; return 0;
}
