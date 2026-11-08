/* All N < m! whose factorial-base digits are all <= B (digit i in 0..min(B,i))
   and which are perfect squares; prints sqrt(N).  128-bit arithmetic, m <= 30. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef unsigned __int128 u128;
static u128 F[40]; static int m,B; static char sq64[64],sq63[63],sq65[65],sq11[11];
static unsigned long long found=0;
static void test(u128 N){
  if(!sq64[N%64]||!sq63[N%63]||!sq65[N%65]||!sq11[N%11]) return;
  long double r=sqrtl((long double)N); u128 s=(u128)r;
  while(s*s>N) s--; while((s+1)*(s+1)<=N) s++;
  if(s*s==N){ unsigned long long hi=(unsigned long long)(s>>64), lo=(unsigned long long)s;
    if(hi) printf("big\n"); else printf("%llu\n",lo); found++; }
}
static void rec(int i,u128 N){
  if(i==0){ test(N); return; }
  int top = B<i?B:i;
  for(int d=0;d<=top;d++) rec(i-1,N+(u128)d*F[i]);
}
int main(int c,char**v){ m=atoi(v[1]); B=atoi(v[2]);
  F[0]=1; for(int i=1;i<40;i++) F[i]=F[i-1]*i;
  for(int x=0;x<64;x++) sq64[(x*x)%64]=1; for(int x=0;x<63;x++) sq63[(x*x)%63]=1;
  for(int x=0;x<65;x++) sq65[(x*x)%65]=1; for(int x=0;x<11;x++) sq11[(x*x)%11]=1;
  rec(m-1,0); fprintf(stderr,"m=%d B=%d found=%llu\n",m,B,found); return 0; }
