/* A185104 sieve.  An n-digit term (n >= 2) has all digits in {1,3,7,9}.
   For moduli m in {7,11,13,37} (10^6 = 1 mod m) the residue of N and of each
   single swap depends only on the counts c[d][r] of digit d in positions
   i = r (mod 6).  Enumerate count vectors class by class; keep a mask of
   residues N must avoid (N itself = 0, or some swap = 0 mod m); prune when a
   mask is full.  Print surviving count vectors. */
#include <stdio.h>
#include <stdlib.h>
static const int D[4]={1,3,7,9};
static const int MO[4]={7,11,13,37};
static int n, s[6], w[4][6];
static int cnt[6][4];
static unsigned long long leaves=0, surv=0;
typedef struct { unsigned long long m[4]; } Mask;
static int full(const Mask*M){ for(int k=0;k<4;k++){ unsigned long long all=(MO[k]==64)?~0ULL:((1ULL<<MO[k])-1); if((M->m[k]&all)==all) return 1;} return 0;}
static void dfs(int r, Mask M){
  if(r==6){
    leaves++;
    int ds=0; for(int q=0;q<6;q++) for(int d=0;d<4;d++) ds+=cnt[q][d]*D[d];
    if(ds%3==0) return;
    for(int k=0;k<4;k++){ int m=MO[k]; long x=0;
      for(int q=0;q<6;q++) for(int d=0;d<4;d++) x+= (long)cnt[q][d]*D[d]*w[k][q];
      x%=m; if((M.m[k]>>x)&1) return; }
    surv++;
    printf("n=%d surv:",n);
    for(int q=0;q<6;q++){ printf(" [");for(int d=0;d<4;d++) printf("%d%s",cnt[q][d],d<3?",":""); printf("]");}
    printf("\n"); return;
  }
  int S=s[r];
  for(int a=0;a<=S;a++) for(int b=0;a+b<=S;b++) for(int c=0;a+b+c<=S;c++){
    int e=S-a-b-c; cnt[r][0]=a;cnt[r][1]=b;cnt[r][2]=c;cnt[r][3]=e;
    Mask N=M;
    for(int d=0;d<4;d++) if(cnt[r][d]) for(int q=0;q<r;q++) for(int d2=0;d2<4;d2++) if(d2!=d && cnt[q][d2]){
      for(int k=0;k<4;k++){ int m=MO[k];
        long x=((long)(D[d]-D[d2])*(w[k][r]-w[k][q]))%m; if(x<0)x+=m;
        N.m[k]|=1ULL<<x; } }
    if(full(&N)) continue;
    dfs(r+1,N);
  }
}
int main(int argc,char**argv){
  n=atoi(argv[1]);
  for(int r=0;r<6;r++) s[r]=0; for(int i=0;i<n;i++) s[i%6]++;
  for(int k=0;k<4;k++){ long p=1; for(int r=0;r<6;r++){ w[k][r]=p; p=p*10%MO[k]; } }
  Mask M; for(int k=0;k<4;k++) M.m[k]=1ULL; /* N != 0 mod m */
  dfs(0,M);
  fprintf(stderr,"n=%d leaves=%llu survivors=%llu\n",n,leaves,surv);
  return 0;
}
