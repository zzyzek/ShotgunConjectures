#include <stdio.h>
#include <stdlib.h>
#include <math.h>
/* For c on a grid, find the smallest n>2 (n<=N) with no m>=1, prime p: n = floor(m^c)+p. */
int main(int argc,char**argv){
  int N=atoi(argv[1]); double c0=atof(argv[2]), c1=atof(argv[3]); int G=atoi(argv[4]);
  char *isp=calloc(N+1,1); for(int i=2;i<=N;i++) isp[i]=1;
  for(long i=2;i*i<=N;i++) if(isp[i]) for(long j=i*i;j<=N;j+=i) isp[j]=0;
  int *v=malloc(sizeof(int)*(N+2));
  for(int g=0;g<=G;g++){
    double c=c0+(c1-c0)*g/G; int K=0;
    for(long m=1;;m++){ double x=floor(pow((double)m,c)); if(x>N) break; v[K++]=(int)x; }
    int bad=0;
    for(int n=3;n<=N;n++){ int ok=0; for(int i=0;i<K && v[i]<n;i++) if(isp[n-v[i]]){ok=1;break;}
      if(!ok && !isp[n]){bad=n;break;} }
    printf("%.10f %d\n",c,bad);
  }
}
