/* For each k <= N with k % 3 == 1: is k = a/b with a, b having ternary digits in {0,1}?
   BFS over carries of the long multiplication k*b (b's digits from the least significant).
   Prints k that fail although k is not in any interval (1.5*3^m, 2*3^m). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int zf(long c){ while(c){ if(c%3==2) return 0; c/=3; } return 1; }
static int interval_bad(long k){ for(long p=1;p<=k;p*=3) if(3*p<2*k && 2*k<4*p) return 1; return 0; }
int main(int argc,char**argv){ long N=atol(argv[1]);
  char *seen=malloc(2*N+10); long *q=malloc(sizeof(long)*(2*N+10));
  for(long k=1;k<=N;k++){ if(k%3!=1) continue;
    memset(seen,0,2*k+4); long h=0,t=0; q[t++]=0; seen[0]=1; int found=0;
    while(h<t && !found){ long s=q[h++]; long c=s>>1; int u=s&1;
      for(int d=0;d<2;d++){ long v=k*d+c; if(v%3==2) continue; long nc=v/3; int nu=u||d;
        if(nu && zf(nc)){ found=1; break; }
        long ns=(nc<<1)|nu; if(!seen[ns]){ seen[ns]=1; q[t++]=ns; } } }
    int ib=interval_bad(k);
    if(found && ib){ printf("CONTRADICTION %ld\n",k); }
    if(!found && !ib) printf("%ld\n",k);
  }
  return 0; }
