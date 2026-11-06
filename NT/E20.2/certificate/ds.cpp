// N_d(n) by memoised DP over recency states (see ds.py). Key: k (3 bits) + base-(d-1)
// digits (count-2) of the k(k-1)/2 pairs in recency order. Open-addressing hash table.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
typedef unsigned long long u64;
int d,n; u64 B; size_t cap; u64*keys; unsigned char*vals; size_t used=0;
static inline size_t h(u64 x){x^=x>>33;x*=0xff51afd7ed558ccdULL;x^=x>>33;x*=0xc4ceb9fe1a85ec53ULL;x^=x>>33;return x&(cap-1);}
u64 enc(int k,const int M[8][8]){u64 key=0;for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)key=key*B+(M[i][j]-2);return key*8+k;}
int f(int k,const int M[8][8]){
  u64 key=enc(k,M)+1; size_t p=h(key);
  while(keys[p]){ if(keys[p]==key) return vals[p]; p=(p+1)&(cap-1);}
  int best=0; int N2[8][8];
  if(k<n){ memcpy(N2,M,sizeof(N2)); for(int i=0;i<k;i++) N2[i][k]=2; int v=1+f(k+1,N2); if(v>best)best=v; }
  for(int i=0;i<k-1;i++){
    bool ok=true; for(int j=i+1;j<k;j++) if(M[i][j]+1>d){ok=false;break;}
    if(!ok) continue;
    int ord[8],m=0; for(int a=0;a<k;a++) if(a!=i) ord[m++]=a; ord[m++]=i;
    for(int p2=0;p2<k;p2++) for(int q=p2+1;q<k;q++){ int a=ord[p2],b=ord[q]; int lo=a<b?a:b, hi=a<b?b:a; int c=M[lo][hi]; if(lo==i) c++; N2[p2][q]=c; }
    int v=1+f(k,N2); if(v>best)best=v;
  }
  if(used*10>cap*7){fprintf(stderr,"table full\n");exit(3);}
  p=h(key); while(keys[p]) p=(p+1)&(cap-1); keys[p]=key; vals[p]=best; used++;
  return best;
}
int main(int argc,char**argv){ d=atoi(argv[1]); n=atoi(argv[2]); B=d-1; cap=1ULL<<atoi(argv[3]);
  keys=(u64*)calloc(cap,8); vals=(unsigned char*)calloc(cap,1); if(!keys||!vals){fprintf(stderr,"alloc\n");return 2;}
  int M[8][8]={{0}}; int r=f(0,M); printf("d=%d n=%d N=%d states=%zu\n",d,n,r,used);
  /* witness: letters named by first appearance; lab[rank] = letter at that recency rank */
  int k=0, lab[8], cur=r, nextlab=0; int N2[8][8];
  printf("witness:");
  while(cur>0){ bool done=false;
    if(k<n){ memcpy(N2,M,sizeof(N2)); for(int i=0;i<k;i++) N2[i][k]=2;
      if(1+f(k+1,N2)==cur){ lab[k]=nextlab++; printf(" %d",lab[k]+1); memcpy(M,N2,sizeof(N2)); k++; cur--; done=true; } }
    for(int i=0;i<k-1&&!done;i++){ bool ok=true; for(int j=i+1;j<k;j++) if(M[i][j]+1>d){ok=false;break;} if(!ok) continue;
      int ord[8],m=0; for(int a=0;a<k;a++) if(a!=i) ord[m++]=a; ord[m++]=i;
      for(int p2=0;p2<k;p2++) for(int q=p2+1;q<k;q++){ int a=ord[p2],b=ord[q]; int lo=a<b?a:b, hi=a<b?b:a; int c=M[lo][hi]; if(lo==i) c++; N2[p2][q]=c; }
      if(1+f(k,N2)==cur){ int nl[8]; for(int p2=0;p2<k;p2++) nl[p2]=lab[ord[p2]]; printf(" %d",lab[i]+1); memcpy(lab,nl,sizeof(nl)); memcpy(M,N2,sizeof(N2)); cur--; done=true; } }
    if(!done){printf(" ERROR\n");return 4;} }
  printf("\n"); return 0; }
