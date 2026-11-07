// A084352: search palindromic brilliant numbers p*q (p <= q primes with the
// same number d of decimal digits) whose factors have all digits >= 4.
// Usage: brill d
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
static int ispal(u128 n){ char b[48]; int k=0; while(n){ b[k++]=n%10; n/=10; } for(int i=0;i<k/2;i++){ if(b[i]!=b[k-1-i]){ return 0; } } return 1; }
static u64 *L; static size_t nL=0, cap=0;
static void gen(u64 v, int left){
  if (left==0) { if(isprime(v)){ if(nL==cap){ cap=cap?2*cap:1024; L=realloc(L,cap*8); } L[nL++]=v; } return; }
  for (int d=4; d<=9; d++) { gen(v*10+d, left-1); }
}
static void pr(u128 n){ char b[48]; int k=0; while(n){ b[k++]='0'+n%10; n/=10; } while(k){ putchar(b[--k]); } }
int main(int argc,char**argv){
  int d=atoi(argv[1]);
  gen(0,d);
  fprintf(stderr,"d=%d primes: %zu\n",d,nL);
  long cnt=0;
  for (size_t i=0;i<nL;i++){
    for (size_t j=i;j<nL;j++){
      u128 n=(u128)L[i]*L[j];
      if (ispal(n)) { pr(n); printf(" = %llu * %llu\n",(unsigned long long)L[i],(unsigned long long)L[j]); fflush(stdout); cnt++; }
    }
  }
  fprintf(stderr,"d=%d found %ld\n",d,cnt);
  return 0;
}
