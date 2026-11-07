/* A101513: rows 1 = {1}, 2 = {2,3}; row n (n >= 3) = the n smallest unused positive integers
 * sharing a prime factor with some element of row n-1.  Simulates rows 3..NROWS by this
 * definition and checks the invariant
 *   (I) row n = P_n ∪ {all composites in (R_{n-1}, R_n]},  P_n = {p prime : 2p in row n-1},
 * where R_n = largest composite in row n.  Prints per-row data for the analytic step
 * (n, R_n, l_n = R_n - R_{n-1}, |P_n|) every 500 rows and at the end, and the first terms.
 * Usage: rows NROWS MAXV
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int *spf; char *used; char *Q;
int main(int argc, char **argv) {
  int NR = atoi(argv[1]); long MAXV = atol(argv[2]);
  spf = calloc(MAXV + 1, sizeof(int)); used = calloc(MAXV + 1, 1); Q = calloc(MAXV + 1, 1);
  for (long i = 2; i <= MAXV; i++) { if (!spf[i]) { for (long j = i; j <= MAXV; j += i) { if (!spf[j]) spf[j] = i; } } }
  long *prev = malloc(sizeof(long) * (NR + 2)), *cur = malloc(sizeof(long) * (NR + 2));
  long *pend = malloc(sizeof(long) * MAXV); long npend = 0;
  /* rows 1, 2 */
  used[1] = used[2] = used[3] = 1;
  prev[0] = 2; prev[1] = 3; int np = 2;
  long frontier = 3, Rprev = 3, Rprevprev = 1;
  long printed = 0;
  printf("terms: 1 2 3");
  for (int n = 3; n <= NR; n++) {
    for (int i = 0; i < np; i++) { long x = prev[i]; while (x > 1) { int p = spf[x]; Q[p] = 1; while (x % p == 0) x /= p; } }
    int nc = 0;
    /* pending (unused numbers below the frontier), in increasing order */
    long keep = 0;
    for (long i = 0; i < npend; i++) {
      long c = pend[i]; int ok = 0;
      if (nc < n) { long x = c; while (x > 1) { int p = spf[x]; if (Q[p]) { ok = 1; break; } while (x % p == 0) x /= p; } }
      if (ok) { cur[nc++] = c; used[c] = 1; } else { pend[keep++] = c; }
    }
    npend = keep;
    while (nc < n) {
      long c = ++frontier;
      if (c > MAXV) { fprintf(stderr, "MAXV too small\n"); return 1; }
      long x = c; int ok = 0;
      while (x > 1) { int p = spf[x]; if (Q[p]) { ok = 1; break; } while (x % p == 0) x /= p; }
      if (ok) { cur[nc++] = c; used[c] = 1; } else { pend[npend++] = c; }
    }
    /* check invariant (I) for row n (n >= 5) */
    long R = 0; int nprime = 0;
    for (int i = 0; i < nc; i++) { long c = cur[i]; if (spf[c] != c && c > R) R = c; }
    if (n >= 5) {
      for (int i = 0; i < nc; i++) {
        long c = cur[i];
        if (spf[c] == c) { nprime++; int in = 0; for (int j = 0; j < np; j++) if (prev[j] == 2 * c) in = 1; if (!in) { printf("\nFAIL prime %ld row %d\n", c, n); return 1; } }
        else if (c <= Rprev) { printf("\nFAIL composite %ld row %d below R_{n-1}\n", c, n); return 1; }
      }
      for (long c = Rprev + 1; c <= R; c++) { if (spf[c] != c && !used[c]) { printf("\nFAIL composite %ld skipped row %d\n", c, n); return 1; } }
      for (int j = 0; j < np; j++) { long e = prev[j]; if (e % 2 == 0 && spf[e / 2] == e / 2) { int in = 0; for (int i = 0; i < nc; i++) if (cur[i] == e / 2) in = 1; if (!in) { printf("\nFAIL 2p=%ld row %d, p not next\n", e, n - 1); return 1; } } }
    }
    if (printed < 72) { for (int i = 0; i < nc && printed < 72 - 3; i++) { printf(" %ld", cur[i]); printed++; } if (printed >= 69) { printf("\n"); printed = 1000; } }
    if (n % 500 == 0 || n == NR) printf("n=%d R=%ld l=%ld |P|=%d pend=%ld\n", n, R, R - Rprev, nprime, npend);
    for (int i = 0; i < np; i++) { long x = prev[i]; while (x > 1) { int p = spf[x]; Q[p] = 0; while (x % p == 0) x /= p; } }
    memcpy(prev, cur, sizeof(long) * nc); np = nc; Rprevprev = Rprev; Rprev = R;
  }
  printf("invariant (I) holds for rows 5..%d\n", NR);
  return 0;
}
