// A085574: find all m = n+1 with P = m^3 - m + e palindromic (e = 0: n(n+1)(n+2) palindrome,
// e = 1: n(n+1)(n+2)+1 palindrome), for P with D digits, Dmin <= D <= Dmax (Dmax <= 38).
// Meet in the middle: the low j digits of P fix (by reversal) its top j digits, hence an interval
// for m; enumerate m by its residue mod 10^j. Work ~ 2*10^(D/6) per D.
//
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128;
static u128 P10[40];
static int ispal(u128 n){ char b[48]; int k=0; while(n){ b[k++]=n%10; n/=10; } for(int i=0;i<k/2;i++){ if(b[i]!=b[k-1-i]){ return 0; } } return 1; }
static int ndig(u128 n){ int k=0; while(n){ k++; n/=10; } return k; }
static void pr(u128 n){ char b[48]; int k=0; if(!n){ putchar('0'); } while(n){ b[k++]='0'+n%10; n/=10; } while(k){ putchar(b[--k]); } }
// floor cube root of x
//
static u128 icbrt(u128 x){
  u128 r=(u128)cbrtl((long double)x);
  while ( (r>0) && (r*r*r>x) ) { r--; }
  while ( (r+1)*(r+1)*(r+1)<=x ) { r++; }
  return r;
}
int main(int argc,char**argv){
  int Dmin=atoi(argv[1]), Dmax=atoi(argv[2]);
  P10[0]=1; for(int i=1;i<40;i++){ P10[i]=P10[i-1]*10; }
  long long hits=0;
  for (int D=Dmin; D<=Dmax; D++){
    int j=D/6; if (j<1) { j=1; }
    u128 M=P10[j];
    for (int e=0;e<=1;e++){
      for (u128 rho=0; rho<M; rho++){
        u128 low=( (rho*rho%M)*rho%M + M - rho + e )%M;
        if (low%10==0) { continue; }
        u128 T=0, t=low; for(int i=0;i<j;i++){ T=T*10+t%10; t/=10; }
        u128 Plo=T*P10[D-j], Phi=(T+1)*P10[D-j];
        u128 mlo=icbrt(Plo), mhi=icbrt(Phi)+2;
        if (mlo>2) { mlo-=2; } else { mlo=0; }
        u128 m0=mlo-(mlo%M)+rho; if (m0<mlo) { m0+=M; }
        for (u128 m=m0; m<=mhi; m+=M){
          if (m<2) { continue; }
          u128 P=m*m*m-m+e;
          if ( (P>=Plo) && (P<Phi) && ispal(P) ) {
            printf("D=%d e=%d n=",D,e); pr(m-1); printf(" P="); pr(P); putchar('\n'); fflush(stdout); hits++;
          }
        }
      }
    }
    fprintf(stderr,"D=%d done (j=%d)\n",D,j);
  }
  fprintf(stderr,"hits %lld\n",hits);
  return 0;
}
