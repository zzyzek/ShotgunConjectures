#include <stdio.h>
#include <stdlib.h>
/* S(1)=seed; S(n)=S(n-1)+S(n-1) mod n. Stable when S(n-1)=c(n+1): then a(n)=c forever. */
int main(int argc,char**argv){ long M=atol(argv[1]); long LIM=atol(argv[2]); long worst=0,ws=0,fail=0;
 for(long s=1;s<=M;s++){ unsigned long long S=s; long n; int ok=0;
  for(n=2;n<LIM;n++){ unsigned long long q=S/(n+1); if(S%(n+1)==0 && (S/(n+1))<(unsigned long long)n){ /* S(n-1)=c(n+1), c<n */ ok=1;break;} S+=S%n; }
  if(!ok){fail++; if(fail<10) printf("seed %ld not stable by %ld\n",s,LIM);} else if(n>worst){worst=n;ws=s;} }
 printf("seeds<=%ld: fail=%ld worst stabilization n=%ld at seed %ld\n",M,fail,worst,ws); return 0;}
