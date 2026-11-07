/* For n = p^2 (p = 16843): compute a(n) = (C(2n,n) - C(2n-2,n-1)) mod n^2 - n - 2 directly,
   via p-adic unit products mod p^4 = n^2 (128-bit arithmetic).
   C(2n,n) = prod_{k=1..n} (n+k)/k ; C(2n-2,n-1) = prod_{k=1..n-1} (n-1+k)/k. */
#include <stdio.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static u64 M;
static u64 mul(u64 a,u64 b){return (u64)((u128)a*b%M);}
static u64 pw(u64 a,u64 e){u64 r=1%M;while(e){if(e&1)r=mul(r,a);a=mul(a,a);e>>=1;}return r;}
static u64 P;
static void acc(u64 x,int sgn,u64*u,long*e){while(x%P==0){x/=P;*e+=sgn;} x%=M; if(sgn>0)*u=mul(*u,x); else *u=mul(*u,x);}
static u64 binom(u64 a,u64 b){ /* C(a,b) mod M, M = P^4 */
  u64 num=1,den=1; long e=0;
  for(u64 k=1;k<=b;k++){ acc(a-b+k,1,&num,&e); acc(k,-1,&den,&e); }
  /* den is a unit mod P^4; inverse via Euler: phi(P^4)=P^3(P-1) */
  u64 inv=pw(den,(u64)P*P*P*(P-1)-1);
  u64 r=mul(num,inv); for(long i=0;i<e;i++) r=mul(r,P);
  if(e<0) {printf("negative valuation?\n");}
  return r;}
int main(int argc,char**argv){ P=16843; u64 n=P*P; M=n*n;
  u64 c1=binom(2*n,n), c2=binom(2*n-2,n-1), c3=binom(2*n-1,n-1);
  u64 d=(c1+M-c2)%M;
  printf("n=%llu C(2n-1,n-1) mod n^2 = %llu ; (C(2n,n)-C(2n-2,n-1)) mod n^2 = %llu ; a(n) = %lld\n",
    (unsigned long long)n,(unsigned long long)c3,(unsigned long long)d,(long long)d-(long long)n-2);
  return 0;}
