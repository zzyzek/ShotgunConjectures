#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef unsigned long long u64;
int main(int c,char**v){ u64 A=strtoull(v[1],0,10), B=strtoull(v[2],0,10); u64 S=1<<22;
 u64 r=(u64)sqrtl((long double)(B+4))+2; char *isc=calloc(r+1,1); u64 *pr=malloc(sizeof(u64)*r); u64 np=0;
 for(u64 i=2;i<=r;i++) if(!isc[i]){pr[np++]=i; for(u64 j=i*i;j<=r;j+=i) isc[j]=1;}
 u64 *ph=malloc(8*(S+3)), *rem=malloc(8*(S+3)); u64 carry[3]={0,0,0}; int havec=0; u64 cnt=0;
 for(u64 lo=A; lo<B; lo+=S){ u64 hi=lo+S+3; /* segment [lo,hi) with overlap 3 */
  for(u64 i=0;i<hi-lo;i++){ph[i]=lo+i; rem[i]=lo+i;}
  for(u64 k=0;k<np;k++){ u64 p=pr[k]; if(p*p>=hi) break; u64 st=((lo+p-1)/p)*p;
    for(u64 x=st;x<hi;x+=p){ u64 i=x-lo; ph[i]-=ph[i]/p; while(rem[i]%p==0) rem[i]/=p; } }
  for(u64 i=0;i<hi-lo;i++) if(rem[i]>1) ph[i]-=ph[i]/rem[i];
  u64 lim=(lo+S<B?S:B-lo);
  for(u64 i=0;i<lim;i++){ u64 n=lo+i; if(ph[i+3]==ph[i]+2){printf("k3 %llu\n",n);fflush(stdout);} if(ph[i]==ph[i+1]&&ph[i+1]==ph[i+2]){printf("trip %llu\n",n);fflush(stdout);} }
 }
 fprintf(stderr,"done\n"); }
