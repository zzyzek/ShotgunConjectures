/* A051924: a(n) = C(2n,n) - C(2n-2,n-1). Check a(n) mod n^2 for n = p^2,
   p = 16843 (Wolstenholme prime). Prediction: a(n) == n+2 (mod n^2).
   C(2n,n) has no factor p here (no carries adding p^2+p^2 in base p),
   so compute it mod p^4 = n^2 as prod_{i=1..n} u(n+i)/u(i), u = p-free part. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static u64 M;
static u64 mul(u64 a,u64 b){return (u64)((u128)a*b%M);}
static u64 pw(u64 a,u64 e){u64 r=1;while(e){if(e&1)r=mul(r,a);a=mul(a,a);e>>=1;}return r;}
/* inverse mod M (M = p^4) via phi(M) = p^3 (p-1) */
int main(int argc,char**argv){
  u64 p=argc>1?strtoull(argv[1],0,10):16843;
  u64 n=p*p; M=n*n; u64 phi=p*p*p*(p-1);
  u64 num=1,den=1; long vnum=0,vden=0;
  for(u64 i=1;i<=n;i++){
    u64 a=n+i,b=i;
    while(a%p==0){a/=p;vnum++;} while(b%p==0){b/=p;vden++;}
    num=mul(num,a%M); den=mul(den,b%M);
  }
  printf("p=%llu n=%llu v_p(C(2n,n))=%ld\n",(unsigned long long)p,(unsigned long long)n,vnum-vden);
  u64 C=mul(num,pw(den,phi-1));               /* C(2n,n) mod n^2 (unit since v=0) */
  /* C(2n-2,n-1) = C(2n,n) * n / (2(2n-1)); n = p^2 so this is exact mod n^2 */
  u64 t=(u64)(((u128)2*((2*n-1)%M))%M);
  u64 C2=mul(mul(C,n%M),pw(t,phi-1));
  u64 a=(C+M-C2)%M;
  printf("a(n) mod n^2 = %llu ; n+2 = %llu ; equal: %d\n",(unsigned long long)a,(unsigned long long)(n+2),a==n+2);
  return 0;
}
