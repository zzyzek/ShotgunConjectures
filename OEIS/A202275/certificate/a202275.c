/* A202275(n) = A074753(n) - A202276(n)
 *   A074753(n) as used by the entry's data = #{k : sigma(k) <= n} (the data of A202275 match
 *   A074753(n+1) - A202276(n); A074753 is now defined with sigma(k) < n),  A202276(n) = n - #{v <= n : v = sigma(k) for some k}.
 * Computes a(n) for 1 <= n <= N, prints the maximum and its positions, the last n with
 * a(n) >= 0, checkpoints of a(n)/n, V(n)/n and C(n)/n, and the first 84 terms.
 * Usage: a202275 N
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  long N = atol(argv[1]);
  uint64_t *s = calloc(N + 1, sizeof(uint64_t));
  uint32_t *mult = calloc(N + 2, sizeof(uint32_t));
  if (!s || !mult) { fprintf(stderr, "alloc\n"); return 1; }
  for (long d = 1; d <= N; d++) { for (long m = d; m <= N; m += d) { s[m] += d; } }
  for (long k = 1; k <= N; k++) { if (s[k] <= (uint64_t)N) { mult[s[k]]++; } }
  free(s);
  /* C(n) = #{k: sigma(k) <= n} = sum_{v<=n} mult[v]; V(n) = #{v<=n : mult[v]>0}. */
  long C = 0, V = 0, best = -1000000000L, lastnonneg = 0, nmax[16]; int nb = 0;
  long chk = 1000;
  for (long n = 1; n <= N; n++) {
    C += mult[n];
    if (mult[n]) { V++; }
    long a = C - (n - V);
    if (n <= 84) { printf("%ld%s", a, n == 84 ? "\n" : ","); }
    if (a > best) { best = a; nb = 0; }
    if (a == best && nb < 16) { nmax[nb++] = n; }
    if (a >= 0) { lastnonneg = n; }
    if (n == chk) { printf("n=%ld a=%ld a/n=%.5f C/n=%.5f V/n=%.5f\n", n, a, (double)a / n, (double)C / n, (double)V / n); chk *= 10; }
  }
  printf("max a(n) = %ld at n =", best);
  for (int i = 0; i < nb; i++) { printf(" %ld", nmax[i]); }
  printf("\nlast n <= %ld with a(n) >= 0: %ld\n", N, lastnonneg);
  return 0;
}
