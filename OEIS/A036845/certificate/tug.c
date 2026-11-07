/* phi/sigma tug-of-war: T1 = phi(n), then sigma, phi, sigma, ...
   For each seed n <= N: iterate f = sigma o phi on the even-index values (y_j = T(n,2j)),
   detect the cycle (Brent), record min/max over all T(n,k).  Factorization: trial division
   by small primes + Pollard rho (u64, __int128).  Memo: per value of y (even-index), cache min/max of
   the forward orbit, by first running until a known value or a cycle is found. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
static u64 mulm(u64 a,u64 b,u64 m){return (u128)a*b%m;}
static u64 powm(u64 a,u64 e,u64 m){u64 r=1;a%=m;while(e){if(e&1)r=mulm(r,a,m);a=mulm(a,a,m);e>>=1;}return r;}
static int isprime(u64 n){ if(n<2)return 0; static const u64 sp[]={2,3,5,7,11,13,17,19,23,29,31,37};
 for(int i=0;i<12;i++){if(n%sp[i]==0)return n==sp[i];}
 u64 d=n-1;int s=0;while(!(d&1)){d>>=1;s++;}
 for(int i=0;i<12;i++){u64 x=powm(sp[i],d,n);if(x==1||x==n-1)continue;int ok=0;for(int r=1;r<s;r++){x=mulm(x,x,n);if(x==n-1){ok=1;break;}}if(!ok)return 0;}
 return 1;}
static u64 gcdu(u64 a,u64 b){while(b){u64 t=a%b;a=b;b=t;}return a;}
static u64 rho(u64 n){ if(n%2==0)return 2; for(u64 c=1;;c++){u64 x=2,y=2,d=1; while(d==1){x=(mulm(x,x,n)+c)%n;y=(mulm(y,y,n)+c)%n;y=(mulm(y,y,n)+c)%n;d=gcdu(x>y?x-y:y-x,n);} if(d!=n)return d;}}
static int np; static u64 P[64]; static int E[64];
static void addp(u64 p){for(int i=0;i<np;i++)if(P[i]==p){E[i]++;return;}P[np]=p;E[np]=1;np++;}
static void fac(u64 n){ if(n==1)return; if(isprime(n)){addp(n);return;} u64 d=rho(n); fac(d); fac(n/d);}
static void factor(u64 n){np=0; static const int sm[]={2,3,5,7,11,13,17,19,23,29,31,37,41,43,47};
 for(int i=0;i<15;i++){while(n%sm[i]==0){addp(sm[i]);n/=sm[i];}} if(n>1)fac(n);}
static int overflow=0;
static u64 phi(u64 n){factor(n);u64 r=n;for(int i=0;i<np;i++)r=r/P[i]*(P[i]-1);return r;}
static u64 sigma(u64 n){factor(n);u128 r=1;for(int i=0;i<np;i++){u128 s=1,pk=1;for(int j=0;j<E[i];j++){pk*=P[i];s+=pk;}r*=s;} if(r>>62){overflow=1;} return (u64)r;}
/* hash memo: key y (even-index value) -> (min,max) of all T values from y onward (y included, and phi(y) etc.) */
#define HB 26
static u64 *hk,*hmin,*hmax; static u64 hmask;
static int hget(u64 k,u64*mn,u64*mx){u64 h=(k*0x9E3779B97F4A7C15ULL)>>(64-HB);while(hk[h]){if(hk[h]==k){*mn=hmin[h];*mx=hmax[h];return 1;}h=(h+1)&hmask;}return 0;}
static u64 hcount=0;
static void hput(u64 k,u64 mn,u64 mx){if(hcount>(hmask/10)*7)return;u64 h=(k*0x9E3779B97F4A7C15ULL)>>(64-HB);while(hk[h]&&hk[h]!=k)h=(h+1)&hmask;if(!hk[h])hcount++;hk[h]=k;hmin[h]=mn;hmax[h]=mx;}
#define MAXPATH 100000
static u64 path[MAXPATH], pmin[MAXPATH], pmax[MAXPATH];
int main(int argc,char**argv){
  u64 N=strtoull(argv[1],0,10);
  hk=calloc(1ULL<<HB,8);hmin=calloc(1ULL<<HB,8);hmax=calloc(1ULL<<HB,8);hmask=(1ULL<<HB)-1;
  u64 gmax=0,gmaxn=0; long maxlen=0; u64 maxlenn=0;
  FILE*fb=fopen("b_check.txt","w");
  for(u64 n=1;n<=N;n++){
    u64 t1=phi(n);
    u64 y=sigma(t1);   /* T(n,2) */
    /* follow y -> sigma(phi(y)) until memo hit or repeat within path */
    long L=0; u64 mn,mx; int hit=0;
    while(1){
      if(hget(y,&mn,&mx)){hit=1;break;}
      for(long i=0;i<L;i++) if(path[i]==y){ /* cycle path[i..L-1] */
          u64 cmn=~0ULL,cmx=0; for(long j=i;j<L;j++){ if(pmin[j]<cmn)cmn=pmin[j]; if(pmax[j]>cmx)cmx=pmax[j]; }
          for(long j=i;j<L;j++) hput(path[j],cmn,cmx);
          L=i; mn=cmn; mx=cmx; hit=1; break; }
      if(hit)break;
      if(L>=MAXPATH){fprintf(stderr,"path too long n=%llu\n",(unsigned long long)n);return 2;}
      u64 z=phi(y); path[L]=y; pmin[L]=y<z?y:z; pmax[L]=y>z?y:z; L++;
      y=sigma(z); if(overflow){fprintf(stderr,"overflow n=%llu\n",(unsigned long long)n);return 3;}
    }
    for(long j=L-1;j>=0;j--){ if(pmin[j]<mn)mn=pmin[j]; if(pmax[j]>mx)mx=pmax[j]; hput(path[j],mn,mx);} 
    if(t1<mn){mn=t1;}
    if(t1>mx){mx=t1;}
    if(L>maxlen){maxlen=L;maxlenn=n;}
    if(mx>gmax){gmax=mx;gmaxn=n;}
    if(n<=16384) fprintf(fb,"%llu %llu %llu\n",(unsigned long long)n,(unsigned long long)mn,(unsigned long long)mx);
    if((n&(n-1))==0 || n==N) {printf("n=%llu  all eventually periodic so far; max T over seeds<=n: %llu (seed %llu); longest new path %ld (seed %llu) memo=%llu\n",(unsigned long long)n,(unsigned long long)gmax,(unsigned long long)gmaxn,maxlen,(unsigned long long)maxlenn,(unsigned long long)hcount);fflush(stdout);}
  }
  fclose(fb);
}
