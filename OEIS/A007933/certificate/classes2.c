/* For each k, count k-digit numbers N (no leading zero) such that some arrangement of the
   digits of N (leading zeros allowed) is prime.  Enumerates digit multisets. Deterministic MR (u64). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static u64 mulm(u64 a,u64 b,u64 m){return (u128)a*b%m;}
static u64 powm(u64 a,u64 e,u64 m){u64 r=1;a%=m;while(e){if(e&1)r=mulm(r,a,m);a=mulm(a,a,m);e>>=1;}return r;}
static int isprime(u64 n){ if(n<2)return 0; static const u64 sp[]={2,3,5,7,11,13,17,19,23,29,31,37};
 for(int i=0;i<12;i++){if(n%sp[i]==0)return n==sp[i];}
 u64 d=n-1;int s=0;while(!(d&1)){d>>=1;s++;}
 for(int i=0;i<12;i++){u64 x=powm(sp[i],d,n);if(x==1||x==n-1)continue;int ok=0;for(int r=1;r<s;r++){x=mulm(x,x,n);if(x==n-1){ok=1;break;}}if(!ok)return 0;}
 return 1;}
static u64 rng=88172645463325252ULL; static u64 xr(){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
static int K; static int cnt[10]; static long double fact[40];
static int nextperm(int*a,int n){int i=n-2;while(i>=0&&a[i]>=a[i+1])i--;if(i<0)return 0;int j=n-1;while(a[j]<=a[i])j--;int t=a[i];a[i]=a[j];a[j]=t;for(int l=i+1,r=n-1;l<r;l++,r--){t=a[l];a[l]=a[r];a[r]=t;}return 1;}
static long exhaustive_calls=0;
static int hasprime(void){
  int a[20],n=0; for(int d=0;d<10;d++)for(int j=0;j<cnt[d];j++)a[n++]=d;
  int S=0; for(int i=0;i<n;i++)S+=a[i];
  int odd=cnt[1]+cnt[3]+cnt[7]+cnt[9];
  int nz=n-cnt[0];
  if(nz==1){int d=0;for(int i=0;i<n;i++)if(a[i])d=a[i];return d==2||d==3||d==5||d==7;}
  if(S%3==0) return 0;            /* every arrangement divisible by 3 and > 3 */
  if(odd==0) return 0;            /* every arrangement ends in 0,2,4,5,6,8 and > 5 */
  for(int tr=0;tr<400;tr++){
    int b[20]; for(int i=0;i<n;i++)b[i]=a[i];
    for(int i=n-1;i>0;i--){int j=xr()%(i+1);int t=b[i];b[i]=b[j];b[j]=t;}
    int last=-1; for(int i=0;i<n;i++)if(b[i]==1||b[i]==3||b[i]==7||b[i]==9){last=i;break;}
    int t=b[n-1];b[n-1]=b[last];b[last]=t;
    u64 v=0;for(int i=0;i<n;i++)v=v*10+b[i];
    if(isprime(v))return 1;
  }
  exhaustive_calls++;
  do{ int l=a[n-1]; if(l==1||l==3||l==7||l==9){u64 v=0;for(int i=0;i<n;i++)v=v*10+a[i];if(isprime(v))return 1;} }while(nextperm(a,n));
  return 0;
}
static long double tot_yes, tot_cop3, tot_ns; static long ns_classes;
static void rec(int d,int left){
  if(d==9){cnt[9]=left;
    if(K>1 && cnt[0]==K) return;
    long double m=fact[K]; for(int i=0;i<10;i++)m/=fact[cnt[i]];
    long double lead0=0; if(cnt[0]>0){lead0=fact[K-1];for(int i=0;i<10;i++)lead0/=fact[cnt[i]-(i==0)];}
    long double c=m-lead0;
    int S=0;for(int i=0;i<10;i++)S+=i*cnt[i];
    if(S%3) tot_cop3+=c;
    int hp=hasprime(); if(hp) tot_yes+=c;
    int odd=cnt[1]+cnt[3]+cnt[7]+cnt[9]; if(!hp && S%3 && odd>0){tot_ns+=c; ns_classes++; if(ns_classes<=40){printf("  fail K=%d counts:",K);for(int q=0;q<10;q++)printf(" %d",cnt[q]);printf("\n");}}
    return;}
  for(int c=0;c<=left;c++){cnt[d]=c;rec(d+1,left-c);}
}
int main(int argc,char**argv){
  int kmax=atoi(argv[1]); fact[0]=1;for(int i=1;i<40;i++)fact[i]=fact[i-1]*i;
  long double cy=0,cc=0;
  for(K=1;K<=kmax;K++){tot_yes=tot_cop3=tot_ns=0;ns_classes=0;exhaustive_calls=0;rec(0,K);cy+=tot_yes;cc+=tot_cop3;
    printf("k=%2d  count_in_[10^(k-1),10^k)=%.0Lf  cumulative A(10^k)=%.0Lf  coprime3_cum=%.0Lf  A/x=%.12Lf  A/coprime3=%.12Lf  deficit=%.0Lf exhaustive=%ld nonstructural_fail_numbers=%.0Lf classes=%ld\n",
      K,tot_yes,cy,cc,cy/powl(10,K),cy/cc,cc-cy,exhaustive_calls,tot_ns,ns_classes);fflush(stdout);}
}
