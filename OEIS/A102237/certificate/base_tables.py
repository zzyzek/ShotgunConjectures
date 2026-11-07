from itertools import combinations
from sympy import primerange
def table(M,L,U):
  ps=list(primerange(3,M+1)); best={}
  for c in combinations(ps,6):
    s=sum(c)
    if L<=s<=U and s not in best: best[s]=list(c)
  out=[]
  for N in range(L,U+1,2):
    assert N in best,(M,N)
    out.append(best[N])
  return out
A=table(39,62,152); B=table(78,62,374)
print(len(A),len(B))
open('baseA.txt','w').write(repr(A)); open('baseB.txt','w').write(repr(B))
# simulate induction with exact real windows, r=1.21, check targets to j=200
r=1.21
for (L,U,M,tgt) in [(62,152,39,lambda j:64*2**j),(62,374,78,lambda j:128*2**j-2)]:
  for j in range(200):
    assert 0.42*M<=1.21*(U-L) and M>=25
    assert L<=tgt(j)<=U,(j,L,U)
    L,U,M=L+r*M,U+2*M/r,2*M
print("ok")
