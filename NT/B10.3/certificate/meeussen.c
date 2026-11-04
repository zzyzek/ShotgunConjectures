/* W(n) = n - d(n) - phi(n) + 1. List odd m < 1000 not attained.
   Bound: odd W needs n even (W >= n/2 - d(n) + 1, d(n) <= 2 sqrt n, so n<=3000 suffices)
   or n an odd square k^2 (W >= k-2 since d(k^2)<=k for odd k), so n <= 1001^2. */
#include <stdio.h>
#include <stdlib.h>
#define N 1100000
int main(void){
  static int phi[N+1], d[N+1]; static char hit[1000];
  for(int i=0;i<=N;i++){phi[i]=i;d[i]=0;}
  for(int i=2;i<=N;i++) if(phi[i]==i) for(int j=i;j<=N;j+=i) phi[j]-=phi[j]/i;
  for(int i=1;i<=N;i++) for(int j=i;j<=N;j+=i) d[j]++;
  for(long n=1;n<=N;n++){ long w=n-d[n]-phi[n]+1; if(w>=0&&w<1000) hit[w]=1; }
  int c=0; for(int m=1;m<1000;m+=2) if(!hit[m]){printf("%d ",m);c++;} printf("\ncount %d\n",c);
  return 0;
}
