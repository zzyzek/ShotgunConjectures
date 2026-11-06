// Mauldon (Guy D16): for each multiplicity m, the smallest S such that
// m triples a<=b<=c of positive integers share sum S and a product,
// and the smallest P such that m triples share product P and a sum.
// usage: triples SMAX PMAX
//
#include <stdio.h>
#include <stdlib.h>

static int cmpll(const void *x, const void *y) {
  long long a = *(const long long *)x, b = *(const long long *)y;
  return ( (a < b) ? -1 : ( (a > b) ? 1 : 0 ) );
}

int main(int argc, char **argv) {
  int SMAX = atoi(argv[1]), PMAX = atoi(argv[2]);
  int S, a, b, n, i, run, best, m, P, nd, d, q, e, j, k, t, p;
  long long *buf = malloc(sizeof(long long) * ((long long)SMAX * SMAX / 4 + 16));
  long long firstS[64] = {0}, firstP[64] = {0};
  int *spf, divs[20000], *sums;

  for (S = 3; S <= SMAX; S++) {
    n = 0;
    for (a = 1; 3 * a <= S; a++) {
      for (b = a; a + 2 * b <= S; b++) {
        buf[n++] = (long long)a * b * (S - a - b);
      }
    }
    qsort(buf, n, sizeof(long long), cmpll);
    best = 1; run = 1;
    for (i = 1; i < n; i++) {
      run = ( (buf[i] == buf[i - 1]) ? (run + 1) : 1 );
      if (run > best) { best = run; }
    }
    for (m = 2; (m <= best) && (m < 64); m++) { if (!firstS[m]) { firstS[m] = S; } }
  }

  spf  = calloc(PMAX + 1, sizeof(int));
  sums = malloc(sizeof(int) * 200000);
  for (i = 2; i <= PMAX; i++) {
    if (!spf[i]) { for (j = i; j <= PMAX; j += i) { if (!spf[j]) { spf[j] = i; } } }
  }
  for (P = 1; P <= PMAX; P++) {
    nd = 1; divs[0] = 1; q = P;
    while (q > 1) {
      p = spf[q]; e = 0;
      while ((q % p) == 0) { q /= p; e++; }
      t = nd;
      for (k = 0; k < t; k++) {
        d = divs[k];
        for (j = 1; j <= e; j++) { d *= p; divs[nd++] = d; }
      }
    }
    n = 0;
    for (i = 0; i < nd; i++) {
      a = divs[i];
      if ( ((long long)a * a * a) > P ) { continue; }
      for (j = 0; j < nd; j++) {
        b = divs[j];
        if ( (b < a) || ((P / a) % b) || ((long long)b * b > (P / a)) ) { continue; }
        sums[n++] = a + b + (P / a) / b;
      }
    }
    best = 0;
    for (i = 0; i < n; i++) {
      run = 0;
      for (j = 0; j < n; j++) { if (sums[j] == sums[i]) { run++; } }
      if (run > best) { best = run; }
    }
    for (m = 2; (m <= best) && (m < 64); m++) { if (!firstP[m]) { firstP[m] = P; } }
  }
  for (m = 2; m < 64; m++) {
    if (firstS[m] || firstP[m]) { printf("m=%d minSum=%lld minProd=%lld\n", m, firstS[m], firstP[m]); }
  }
  return 0;
}
