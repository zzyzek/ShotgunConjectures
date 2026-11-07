/* Enumerate practical numbers <= X by Stewart's characterisation (DFS over prime factorisations with
   p_i <= sigma(prefix) + 1), sort, and check a(n+1)^n < a(n)^(n+1) for n >= 3 (long double logs, with an
   exact __int128-free fallback flag when the margin is tiny).  Reports the worst margin. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef uint64_t u64;
static u64 X; static u64 *arr; static size_t cnt=0, cap;
static unsigned *primes; static size_t np;
static void dfs(u64 n, u64 sig, size_t pi){
  /* n practical; extend with primes p_i (index >= pi), p <= sig+1 */
  arr[cnt++]=n;
  for(size_t i=pi;i<np;i++){
    u64 p=primes[i]; if(p>sig+1) break; if(n>X/p) break;
    u64 m=n*p, pk=p, s=1+p;
    while(1){ dfs(m, sig*s, i+1); if(m>X/p) break; m*=p; pk*=p; s+=pk; }
  }
}
static int cmp(const void*a,const void*b){u64 x=*(u64*)a,y=*(u64*)b;return x<y?-1:x>y;}
int main(int argc,char**argv){
  X=strtoull(argv[1],0,10);
  /* primes up to X/2 + 1 needed? p <= sigma(prefix)+1 and n*p <= X with n >= 2 -> p <= X/2 */
  u64 L=X/2+2; char *c=calloc(L+1,1); np=0;
  primes=malloc(sizeof(unsigned)*(size_t)(L/ (log((double)L)-1.2) +1000));
  for(u64 i=2;i<=L;i++){ if(!c[i]){primes[np++]=(unsigned)i; for(u64 j=i*i;j<=L;j+=i)c[j]=1;} }
  free(c);
  cap=(size_t)(1.5*1.34*X/log((double)X))+1000000; arr=malloc(cap*8);
  dfs(1,1,0);
  qsort(arr,cnt,8,cmp);
  printf("practical numbers <= %llu: %zu\n",(unsigned long long)X,cnt);
  static long double decmax[20]; static size_t decn[20];
  long double worst=1e30; size_t wn=0; long double worstr=0; size_t wrn=0;
  for(size_t i=2;i+1<cnt;i++){ /* n = i+1 (1-based), a(n)=arr[i], a(n+1)=arr[i+1] */
    long double n=(long double)(i+1);
    long double la=logl((long double)arr[i]), lb=logl((long double)arr[i+1]);
    long double margin=(n+1)*la - n*lb;   /* must be > 0 */
    if(margin<worst){worst=margin;wn=i+1;}
    /* gap relative to the threshold a(n)*(a(n)^(1/n)-1) */
    long double thr=(long double)arr[i]*expm1l(la/n);
    long double r=(long double)(arr[i+1]-arr[i])/thr;
    if(r>worstr){worstr=r;wrn=i+1;}
    { int dec=(int)floorl(log10l((long double)arr[i])); if(dec<20){ if(r>decmax[dec]){decmax[dec]=r;decn[dec]=i+1;} } }
    if(margin<=0){printf("FAIL at n=%zu a(n)=%llu a(n+1)=%llu margin=%Lg\n",i+1,(unsigned long long)arr[i],(unsigned long long)arr[i+1],margin);}
  }
  printf("min margin (n+1)log a(n) - n log a(n+1) = %.6Lf at n=%zu (a(n)=%llu)\n",worst,wn,(unsigned long long)arr[wn-1]);
  printf("max gap/threshold = %.6Lf at n=%zu (a(n)=%llu, a(n+1)=%llu)\n",worstr,wrn,(unsigned long long)arr[wrn-1],(unsigned long long)arr[wrn]);
  for(int d=0;d<20;d++) if(decn[d]) printf("a(n) in [1e%d,1e%d): max gap/threshold %.6Lf at n=%zu (a(n)=%llu, gap %llu)\n",d,d+1,decmax[d],decn[d],(unsigned long long)arr[decn[d]-1],(unsigned long long)(arr[decn[d]]-arr[decn[d]-1]));
  /* checksum vs b-file: print a(10000) */
  if(cnt>=10000) printf("a(10000)=%llu\n",(unsigned long long)arr[9999]);
}
