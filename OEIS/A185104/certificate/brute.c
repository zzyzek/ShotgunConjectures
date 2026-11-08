/* Independent brute force: all n-digit numbers over {1,3,7,9}; a number
   survives if N and every single swap have no prime factor < 1000 (and is
   reported).  Survivors are then tested fully in Python. */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u64;
static int P[200],np=0;
static int smallfac(u64 x){ for(int k=0;k<np;k++){ if(x%P[k]==0) return x!=(u64)P[k]; } return 0; }
int main(int argc,char**argv){
  int n=atoi(argv[1]); const int D[4]={1,3,7,9};
  for(int p=2;p<1000;p++){int ok=1;for(int q=2;q*q<=p;q++) if(p%q==0){ok=0;break;} if(ok) P[np++]=p;}
  u64 pw[20]; pw[0]=1; for(int i=1;i<20;i++) pw[i]=pw[i-1]*10;
  u64 total=1; for(int i=0;i<n;i++) total*=4;
  int dig[20];
  for(u64 c=0;c<total;c++){
    u64 t=c,N=0; for(int i=0;i<n;i++){ dig[i]=D[t&3]; t>>=2; N+=dig[i]*pw[i]; }
    if(smallfac(N)) continue;
    int dead=0;
    for(int i=0;i<n&&!dead;i++) for(int j=i+1;j<n;j++) if(dig[i]!=dig[j]){
      u64 M=N+(u64)((long long)(dig[j]-dig[i])*(long long)pw[i])+0; /* placeholder */
      M = N - dig[i]*pw[i] - dig[j]*pw[j] + dig[j]*pw[i] + dig[i]*pw[j];
      if(smallfac(M)){dead=1;break;}
    }
    if(!dead) printf("%llu\n",N);
  }
  return 0;
}
