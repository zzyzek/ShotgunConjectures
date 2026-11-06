// Guy D16, product version.
// For every P in [PLO, PHI], list the triples a <= b <= c with abc = P,
// group them by a+b+c, and record
//   - atleast[m]: the least P that has some sum shared by >= m triples,
//   - exact[s]:   the least P that has some sum shared by exactly s triples
//                 (the A103277 "exactly" convention, with P in place of the sum).
// Every P is factored by a segmented sieve; P is skipped only when its total
// number of triples is below every target still open, so the search is exhaustive.
//
// usage: prodsearch PLO PHI
// output: one line per new record, with the triples.
//
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

#define SEG    (1 << 20)
#define MAXF   16
#define MAXD   65536
#define MAXT   400000
#define MAXM   64

typedef uint64_t u64;

static u64   *primes; static int np;
static u64    rem_[SEG];
static u64    fp_[SEG][MAXF];
static int    fe_[SEG][MAXF];
static int    nf_[SEG];
static u64    atleast[MAXM], exact[MAXM];
static u64    divs[MAXD];
static u64    ta[MAXT], tb[MAXT], tc[MAXT], ts[MAXT];
static int    idx[MAXT];

static int cmpidx(const void *x, const void *y) {
  u64 a = ts[*(const int *)x], b = ts[*(const int *)y];
  return ( (a < b) ? -1 : ( (a > b) ? 1 : 0 ) );
}

static u64 isqrt64(u64 n) {
  u64 r = (u64)sqrtl((long double)n);
  while ( (r * r) > n ) { r--; }
  while ( ((r + 1) * (r + 1)) <= n ) { r++; }
  return r;
}

static u64 icbrt64(u64 n) {
  u64 r = (u64)cbrtl((long double)n);
  while ( (r * r * r) > n ) { r--; }
  while ( ((r + 1) * (r + 1) * (r + 1)) <= n ) { r++; }
  return r;
}

// Divisors of the number with primes p[0..k-1] and exponents e[0..k-1].
//
static int gendivs(const u64 *p, const int *e, int k, u64 *out) {
  int n = 1, i, j, t, l;
  u64 d;
  out[0] = 1;
  for (i = 0; i < k; i++) {
    t = n;
    for (l = 0; l < t; l++) {
      d = out[l];
      for (j = 1; j <= e[i]; j++) { d *= p[i]; out[n++] = d; }
    }
  }
  return n;
}

int main(int argc, char **argv) {
  u64 PLO = strtoull(argv[1], 0, 10), PHI = strtoull(argv[2], 0, 10);
  u64 sq = isqrt64(PHI) + 1, L, P, p, q, a, b, Q, sqQ, cb, s0, m0;
  char *comp = calloc(sq + 1, 1);
  int i, j, k, n, nd, nt, nb, run, need, best, mtarget, etarget, e, ea[MAXF], eq[MAXF];
  u64 qd[MAXD];
  long long cnt[MAXM];

  primes = malloc(sizeof(u64) * (sq + 1)); np = 0;
  for (i = 2; (u64)i <= sq; i++) {
    if (!comp[i]) {
      primes[np++] = i;
      for (j = 2 * i; (u64)j <= sq; j += i) { comp[j] = 1; }
    }
  }
  memset(atleast, 0, sizeof(atleast)); memset(exact, 0, sizeof(exact));

  for (L = PLO; L <= PHI; L += SEG) {
    u64 W = ( ((PHI - L + 1) < SEG) ? (PHI - L + 1) : SEG );
    for (i = 0; (u64)i < W; i++) { rem_[i] = L + i; nf_[i] = 0; }
    for (k = 0; k < np; k++) {
      p = primes[k];
      if ( (p * p) > (L + W - 1) ) { break; }
      u64 st = ( ((L % p) == 0) ? L : (L + p - (L % p)) );
      for (P = st; P < L + W; P += p) {
        i = (int)(P - L); e = 0;
        while ( (rem_[i] % p) == 0 ) { rem_[i] /= p; e++; }
        fp_[i][nf_[i]] = p; fe_[i][nf_[i]] = e; nf_[i]++;
      }
    }

    // Smallest targets still open.
    //
    for (mtarget = 2; (mtarget < MAXM) && atleast[mtarget]; mtarget++) { }
    for (etarget = 2; (etarget < MAXM) && exact[etarget]; etarget++) { }
    need = ( (mtarget < etarget) ? mtarget : etarget );

    for (i = 0; (u64)i < W; i++) {
      P = L + i;
      if (P < 2) { continue; }
      if (rem_[i] > 1) { fp_[i][nf_[i]] = rem_[i]; fe_[i][nf_[i]] = 1; nf_[i]++; }

      // Upper bound on the number of triples: (tau3 + 3 tau + 2) / 6.
      //
      {
        u64 t3 = 1, t1 = 1;
        for (j = 0; j < nf_[i]; j++) {
          t3 *= (u64)(fe_[i][j] + 1) * (fe_[i][j] + 2) / 2;
          t1 *= (u64)(fe_[i][j] + 1);
        }
        if ( ((t3 + (3 * t1) + 2) / 6) < (u64)need ) { continue; }
      }

      nd = gendivs(fp_[i], fe_[i], nf_[i], divs);
      cb = icbrt64(P); nt = 0;
      for (j = 0; j < nd; j++) {
        a = divs[j];
        if (a > cb) { continue; }
        Q = P / a; sqQ = isqrt64(Q);

        // Exponents of Q = P / a.
        //
        q = a;
        for (k = 0; k < nf_[i]; k++) {
          ea[k] = 0;
          while ( (q % fp_[i][k]) == 0 ) { q /= fp_[i][k]; ea[k]++; }
          eq[k] = fe_[i][k] - ea[k];
        }
        nb = gendivs(fp_[i], eq, nf_[i], qd);
        for (k = 0; k < nb; k++) {
          b = qd[k];
          if ( (b < a) || (b > sqQ) ) { continue; }
          if (nt >= MAXT) { fprintf(stderr, "MAXT overflow at %llu\n", (unsigned long long)P); return 2; }
          ta[nt] = a; tb[nt] = b; tc[nt] = Q / b; ts[nt] = a + b + (Q / b); idx[nt] = nt; nt++;
        }
      }
      if (nt < need) { continue; }
      qsort(idx, nt, sizeof(int), cmpidx);
      memset(cnt, 0, sizeof(cnt));
      best = 0;
      for (j = 0; j < nt; j = k) {
        for (k = j; (k < nt) && (ts[idx[k]] == ts[idx[j]]); k++) { }
        run = k - j;
        if (run > best) { best = run; }
        if (run < MAXM) {
          if (!exact[run]) {
            exact[run] = P;
            printf("EXACT s=%d P=%llu S=%llu :", run, (unsigned long long)P, (unsigned long long)ts[idx[j]]);
            for (n = j; n < k; n++) {
              printf(" %llu,%llu,%llu", (unsigned long long)ta[idx[n]], (unsigned long long)tb[idx[n]], (unsigned long long)tc[idx[n]]);
            }
            printf("\n"); fflush(stdout);
          }
        }
      }
      for (j = 2; (j <= best) && (j < MAXM); j++) {
        if (!atleast[j]) {
          atleast[j] = P;
          printf("ATLEAST m=%d P=%llu\n", j, (unsigned long long)P); fflush(stdout);
        }
      }
      for (mtarget = 2; (mtarget < MAXM) && atleast[mtarget]; mtarget++) { }
      for (etarget = 2; (etarget < MAXM) && exact[etarget]; etarget++) { }
      need = ( (mtarget < etarget) ? mtarget : etarget );
    }
    if ( ((L / SEG) % 256) == 0 ) {
      fprintf(stderr, "progress L=%llu need=%d\n", (unsigned long long)L, need);
    }
  }
  printf("DONE %llu %llu\n", (unsigned long long)PLO, (unsigned long long)PHI);
  return 0;
}
