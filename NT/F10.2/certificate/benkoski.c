// odd n = 9 mod 10 with 2^n = 4 mod n  (Benkoski / Zhang Ming-Zhi question, UPINT F10)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int c,char**v){ uint64_t N=strtoull(v[1],0,10), lo=c>2?strtoull(v[2],0,10):9;
 for(uint64_t n=lo;n<=N;n+=10){ uint64_t r=1,b=2%n,e=n;
  while(e){ if(e&1) r=r*b%n; b=b*b%n; e>>=1; }
  if(r==4%n) printf("%llu\n",(unsigned long long)n); }
 return 0;}
