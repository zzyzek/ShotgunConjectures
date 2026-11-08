/* For every odd composite x with 27 <= x < XMAX, find an even e with 8 <= e <= EMAX, e < x,
   e+1 and e+25 composite, and x+e prime.  Segmented sieve.  Reports max witness and failures. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
#define EMAX 4000
static int isp_small(u64 n){ if(n<2) return 0; for(u64 d=2; d*d<=n; d++) if(n%d==0) return 0; return 1; }
int main(int argc, char **argv){
  u64 XMAX = strtoull(argv[1],0,10), SEG = 1ULL<<24;
  int W[EMAX], nw=0;
  for(int e=8;e<=EMAX;e+=2) if(!isp_small(e+1) && !isp_small(e+25)) W[nw++]=e;
  u64 lim = 1; while(lim*lim <= XMAX+EMAX+1) lim++;
  char *bs = calloc(lim+1,1); u64 *bp = malloc(sizeof(u64)*lim); int nb=0;
  for(u64 i=2;i<=lim;i++) if(!bs[i]){ bp[nb++]=i; for(u64 j=i*i;j<=lim;j+=i) bs[j]=1; }
  char *comp = malloc(SEG+EMAX+16);
  u64 maxw=0, maxx=0, fails=0, checked=0;
  for(u64 lo=0; lo<XMAX; lo+=SEG){
    u64 hi = lo+SEG+EMAX+2;   /* sieve [lo, hi) */
    memset(comp,0,hi-lo);
    for(int k=0;k<nb;k++){ u64 p=bp[k]; if(p*p>=hi) break;
      u64 s = (lo+p-1)/p*p; if(s<p*p) s=p*p; for(u64 j=s;j<hi;j+=p) comp[j-lo]=1; }
    if(lo==0){ comp[0]=comp[1]=1; }
    u64 xs = lo<27?27:lo; if(xs%2==0) xs++;
    u64 xe = lo+SEG<XMAX?lo+SEG:XMAX;
    for(u64 x=xs;x<xe;x+=2){
      if(!comp[x-lo]) continue;
      checked++;
      int ok=0;
      for(int i=0;i<nw;i++){ u64 e=W[i]; if(e>=x) break; if(!comp[x+e-lo]){ ok=1; if(e>maxw){maxw=e;maxx=x;} break; } }
      if(!ok){ fails++; if(fails<20) printf("FAIL x=%llu\n",(unsigned long long)x); }
    }
  }
  printf("XMAX=%llu checked=%llu fails=%llu maxwitness=%llu at x=%llu\n",(unsigned long long)XMAX,(unsigned long long)checked,(unsigned long long)fails,(unsigned long long)maxw,(unsigned long long)maxx);
  return 0;
}
