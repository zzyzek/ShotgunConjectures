#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef unsigned int u;
int main(int c,char**v){ u N=atol(v[1]); u *p=malloc(sizeof(u)*(N+2));
 for(u i=0;i<=N;i++)p[i]=i;
 for(u i=2;i<=N;i++) if(p[i]==i) for(u j=i;j<=N;j+=i) p[j]-=p[j]/i;
 /* suffix min, valid bound B: phi(m)>=B for all m>N (Rosser-Schoenfeld) */
 double ll=log(log((double)N)); double B=N/(exp(0.5772156649)*ll+2.50637/ll);
 u *sm=malloc(sizeof(u)*(N+2)); sm[N+1]=0xffffffffu; for(long i=N;i>=1;i--){ u a=p[i]; sm[i]=(a<sm[i+1]?a:sm[i+1]);}
 u last=0; long cnt=0,odd=0,not30=0;
 for(u n=1;n<=N;n++){ if(p[n]>=B) break; /* beyond certified region */
   if(p[n]<=sm[n+1] || n==N){ if(p[n]!=last){ cnt++; last=p[n]; printf("%u %u\n",n,p[n]);} } }
 fprintf(stderr,"B=%f\n",B); }
