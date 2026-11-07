/* Tabu search for a rosary of length L over [n]. Usage: tabu n L seed steps */
#include <stdio.h>
#include <stdlib.h>
int n,L; int perms[40320][8]; int np=0; int w[200]; int nxt[200][8]; int tabu[200][8];
void genp(int *a,int k){ if(k==n){ for(int i=0;i<n;i++) perms[np][i]=a[i]; np++; return; }
  for(int i=k;i<n;i++){ int t=a[k];a[k]=a[i];a[i]=t; genp(a,k+1); t=a[k];a[k]=a[i];a[i]=t; } }
void build(){ for(int c=0;c<n;c++){ int last=-1; for(int j=2*L-1;j>=0;j--){ if(w[j%L]==c) last=j; if(j<L) nxt[j][c]=(last<0?100000:last-j); } } }
int covered(int *p){ for(int s=0;s<L;s++){ int pos=s, used=0, ok=1;
    for(int k=0;k<n;k++){ int d=nxt[pos%L][p[k]]; if(d>=100000){ok=0;break;} used+=d+1; pos+=d+1; if(used>L){ok=0;break;} }
    if(ok) return 1; } return 0; }
int score(int cap){ build(); int u=0; for(int i=0;i<np;i++) if(!covered(perms[i])){ u++; if(u>=cap) return u; } return u; }
int main(int argc,char**argv){ n=atoi(argv[1]); L=atoi(argv[2]); srand(atoi(argv[3])); long steps=atol(argv[4]);
  int a[8]; for(int i=0;i<n;i++) a[i]=i; genp(a,0);
  for(int i=0;i<L;i++) w[i]=rand()%n;
  int s=score(1<<30), best=s;
  for(long t=1;t<=steps && s>0;t++){
    int bi=-1,bc=-1,bs=1<<30;
    for(int i=0;i<L;i++) for(int c=0;c<n;c++){ if(c==w[i]) continue;
      int old=w[i]; w[i]=c; int s2=score(bs+1); w[i]=old;
      int asp = (s2<best);
      if((tabu[i][c]>t) && !asp) continue;
      if(s2<bs || (s2==bs && rand()%2)){ bs=s2; bi=i; bc=c; } }
    if(bi<0) continue;
    tabu[bi][w[bi]] = t + 5 + rand()%10; w[bi]=bc; s=bs; if(s<best){ best=s; fprintf(stderr,"t=%ld best=%d\n",t,best);} }
  printf("n=%d L=%d final=%d best=%d word:",n,L,s,best); for(int i=0;i<L;i++) printf(" %d",w[i]+1); printf("\n"); return s!=0; }
