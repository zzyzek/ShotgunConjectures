/* A083125: a(1)=1; a(k+1) = least unused m with a(k)*m a palindrome.
   Enumerates palindromes P >= a(k) in increasing order, tests a(k) | P and P/a(k) unused.
   Reports the least non-multiple of 10 not yet used at checkpoints. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define LIM 1000000000ULL
static unsigned char *bits;
static int used(uint64_t m){ if(m>=LIM){fprintf(stderr,"overflow %llu\n",(unsigned long long)m);exit(2);} return bits[m>>3]>>(m&7)&1; }
static void mark(uint64_t m){ bits[m>>3]|=1<<(m&7); }
static uint64_t mkpal(uint64_t h,int len){ /* h has ceil(len/2) digits */
  uint64_t p=h, t=(len&1)? h/10 : h; while(t){p=p*10+t%10;t/=10;} return p; }
int main(int argc,char**argv){
  long N=atol(argv[1]); bits=calloc(LIM/8+1,1);
  uint64_t a=1, amax=1; mark(1); uint64_t lowfree=2; long maxwait=0;
  if(N<=40) printf("1");
  for(long k=2;k<=N;k++){
    uint64_t best=0;
    for(int len=1;len<=19 && !best;len++){
      int hl=(len+1)/2; uint64_t lo=1,hi; for(int i=1;i<hl;i++) lo*=10; hi=lo*10;
      for(uint64_t h=lo;h<hi;h++){ uint64_t P=mkpal(h,len); if(P<a) continue;
        if(P%a==0){ uint64_t m=P/a; if(!used(m)){best=m;break;} } }
    }
    if(!best){fprintf(stderr,"no palindrome found at k=%ld a=%llu\n",k,(unsigned long long)a);return 1;}
    a=best; mark(a); if(a>amax) amax=a;
    if(N<=40) printf(",%llu",(unsigned long long)a);
    while(used(lowfree)||lowfree%10==0) lowfree++;
    if(k%20000==0||k==N) { fprintf(stdout,"k=%ld a=%llu least_missing_non_mult10=%llu\n",k,(unsigned long long)a,(unsigned long long)lowfree); fflush(stdout);}
  }
  printf("max term %llu\n",(unsigned long long)amax); printf("missing non-multiples of 10 below 2000:"); for(uint64_t m=1;m<2000;m++) if(m%10 && !used(m)) printf(" %llu",(unsigned long long)m); printf("\n"); return 0; }
