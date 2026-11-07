// smallest x <= LIM with tau(x)/tau(x-1) = n, for each n; report whether x-1 is prime
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  long LIM=atol(argv[1]);
  uint16_t *t=calloc(LIM+1,2);
  for(long d=1;d<=LIM;d++) for(long m=d;m<=LIM;m+=d) t[m]++;
  long best[2000]={0};
  for(long x=3;x<=LIM;x++){ if(t[x]%t[x-1]==0){int n=t[x]/t[x-1]; if(n<2000&&!best[n]) best[n]=x;}}
  for(int n=1;n<2000;n++) if(best[n]) printf("%d %ld tau(x-1)=%d %s\n",n,best[n],t[best[n]-1],t[best[n]-1]==2?"prime":"NOTPRIME");
  return 0;}
