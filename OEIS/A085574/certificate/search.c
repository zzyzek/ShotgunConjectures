// A085574: list n <= N with n(n+1)(n+2) or n(n+1)(n+2)+1 a palindrome.
// Usage: search N
//
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int ispal(u128 n){ char b[48]; int k=0; while(n){ b[k++]=n%10; n/=10; } for(int i=0;i<k/2;i++){ if(b[i]!=b[k-1-i]){ return 0; } } return 1; }
static void pr(u128 n){ char b[48]; int k=0; if(!n){ putchar('0'); } while(n){ b[k++]='0'+n%10; n/=10; } while(k){ putchar(b[--k]); } }
int main(int argc,char**argv){
  uint64_t N=strtoull(argv[1],0,10);
  for (uint64_t n=1;n<=N;n++){
    u128 v=(u128)n*(n+1)*(n+2);
    // Quick filter: first and last digits must agree for v or v+1.
    //
    unsigned l0=(unsigned)(v%10), l1=(unsigned)((v+1)%10);
    u128 t=v; while(t>=10){ t/=10; }
    unsigned f=(unsigned)t;
    if ( (f==l0) && ispal(v) ) { printf("n=%llu k=0 ",(unsigned long long)n); pr(v); putchar('\n'); fflush(stdout); }
    if ( ispal(v+1) ) { printf("n=%llu k=1 ",(unsigned long long)n); pr(v+1); putchar('\n'); fflush(stdout); }
    (void)l1;
  }
  return 0;
}
