// Search palindromic semiprimes p*q (p <= q primes) whose prime factors
// have all decimal digits >= 4 (A084189: claim min digit never > 3).
// Usage: search X   (X <= 1.8e19)
//
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
typedef uint64_t u64;
static u64 mulmod(u64 a,u64 b,u64 m){ return (u128)a*b%m; }
static u64 powmod(u64 a,u64 e,u64 m){ u64 r=1; a%=m; while(e){ if(e&1){r=mulmod(r,a,m);} a=mulmod(a,a,m); e>>=1; } return r; }
static int isprime(u64 n){
  if (n<2) { return 0; }
  static const u64 sp[]={2,3,5,7,11,13,17,19,23,29,31,37};
  for (int i=0;i<12;i++){ if(n%sp[i]==0){ return n==sp[i]; } }
  u64 d=n-1; int s=0; while((d&1)==0){ d>>=1; s++; }
  for (int i=0;i<12;i++){
    u64 x=powmod(sp[i],d,n);
    if (x==1 || x==n-1) { continue; }
    int ok=0;
    for (int r=1;r<s;r++){ x=mulmod(x,x,n); if(x==n-1){ ok=1; break; } }
    if (!ok) { return 0; }
  }
  return 1;
}
static int ispal(u64 n){ char b[32]; int k=0; while(n){ b[k++]=n%10; n/=10; } for(int i=0;i<k/2;i++){ if(b[i]!=b[k-1-i]){ return 0; } } return 1; }
static int ndig(u64 n){ int k=0; while(n){ k++; n/=10; } return k; }
static u64 *L; static size_t nL=0, cap=0;
static void gen(u64 v, u64 lim){
  if (v>lim) { return; }
  if (v && isprime(v)) { if(nL==cap){ cap=cap?2*cap:1024; L=realloc(L,cap*8); } L[nL++]=v; }
  if (v > lim/10) { return; }
  for (int d=4; d<=9; d++) { gen(v*10+d, lim); }
}
static int cmp(const void*a,const void*b){ u64 x=*(u64*)a,y=*(u64*)b; return (x>y)-(x<y); }
int main(int argc,char**argv){
  u64 X=strtoull(argv[1],0,10);
  gen(0, X/5);
  qsort(L,nL,8,cmp);
  fprintf(stderr,"primes: %zu\n",nL);
  for (size_t i=0;i<nL;i++){
    u64 p=L[i]; if ((u128)p*p > X) { break; }
    for (size_t j=i;j<nL;j++){
      u128 n=(u128)p*L[j]; if (n>X) { break; }
      if (ispal((u64)n)) { printf("%llu = %llu * %llu%s\n",(unsigned long long)n,(unsigned long long)p,(unsigned long long)L[j], ndig(p)==ndig(L[j])?" brilliant":""); fflush(stdout); }
    }
  }
  return 0;
}
