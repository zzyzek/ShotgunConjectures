/* Density of A214620 (same lpf, gpf, bit length and popcount as another m) and
   A214621 (additionally the same decimal digit multiset) among n < N.
   Membership: key class has >= 2 elements. Reports fraction in each dyadic block [2^(L-1), 2^L)
   (A214620) and decade [10^(d-1), 10^d) (A214621). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef struct { uint64_t a, b; uint32_t n; } K;
static int cmp(const void *x, const void *y) {
  const K *p = x, *q = y;
  if (p->a != q->a) return p->a < q->a ? -1 : 1;
  if (p->b != q->b) return p->b < q->b ? -1 : 1;
  return 0;
}
int main(int argc, char **argv) {
  long N = atol(argv[1]);
  uint32_t *lpf = calloc(N, 4), *gpf = calloc(N, 4);
  for (long i = 2; i < N; i++) if (!lpf[i]) for (long j = i; j < N; j += i) { if (!lpf[j]) lpf[j] = i; gpf[j] = i; }
  K *k = malloc(sizeof(K) * N);
  for (int mode = 0; mode < 2; mode++) {
    long m = 0;
    for (long n = 2; n < N; n++) {
      int L = 64 - __builtin_clzll(n), pc = __builtin_popcountll(n);
      uint64_t dig = 0; int dl = 0;
      if (mode) { long t = n; while (t) { dig += 1ULL << (4 * (t % 10)); t /= 10; dl++; } }
      k[m].a = ((uint64_t)L << 58) | ((uint64_t)pc << 52) | ((uint64_t)dl << 46) | (dig & ((1ULL << 46) - 1));
      k[m].b = ((uint64_t)lpf[n] << 32) | gpf[n];
      k[m].a ^= (dig >> 46) << 40;
      k[m].n = n; m++;
    }
    qsort(k, m, sizeof(K), cmp);
    char *in = calloc(N, 1);
    for (long i = 0; i < m; ) {
      long j = i; while (j < m && k[j].a == k[i].a && k[j].b == k[i].b) j++;
      if (j - i >= 2) for (long t = i; t < j; t++) in[k[t].n] = 1;
      i = j;
    }
    if (!mode) {
      for (int L = 4; (1L << (L - 1)) < N; L++) {
        long lo = 1L << (L - 1), hi = (1L << L) < N ? (1L << L) : N, c = 0;
        for (long n = lo; n < hi; n++) c += in[n];
        printf("A214620 [2^%d,2^%d) frac %.4f\n", L - 1, L, (double)c / (hi - lo));
      }
    } else {
      for (long lo = 10; lo < N; lo *= 10) {
        long hi = lo * 10 < N ? lo * 10 : N, c = 0;
        for (long n = lo; n < hi; n++) c += in[n];
        printf("A214621 [%ld,%ld) frac %.4f\n", lo, hi, (double)c / (hi - lo));
      }
    }
    free(in);
  }
  return 0;
}
