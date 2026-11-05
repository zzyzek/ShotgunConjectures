# Find the telescoping certificate G for A124431 by linear algebra: G(n,i)/2^(n-2i)
# is a combination of products C(n-i-a, i-b) C(n-i-a2, i-b2) with polynomial
# coefficients of total degree <= DEG in (n, i), fitted to the partial sums
# G(n,i) = sum_{i'<i} F(n,i'), F = Mathar operator applied to w(., i).
# Usage: python3 find_certificate.py DEG AMAX BSET NROWS  (used: 1 4 0,1 50)
#
import sys
from fractions import Fraction as F
from math import comb
def C(a,b): return comb(a,b) if (a>=0 and 0<=b<=a) else 0
def w(n,i):
  if n<0 or 2*i>n+1: return 0
  return F(2)**(n-2*i)*(C(n-i,i)**2 + 2*C(n-i,i-1)*C(n-i+1,i))
c=lambda n:[n+1,-2*(2*n+1),2*(n-1),2*(5-2*n),n-3]
DEG=int(sys.argv[1]); AMAX=int(sys.argv[2]); BSET=[int(x) for x in sys.argv[3].split(',')]
basis=[(a,b,a2,b2) for a in range(0,AMAX+1) for a2 in range(a,AMAX+1) for b in BSET for b2 in BSET if (a<a2 or b<=b2)]
mons=[(p,q) for p in range(DEG+1) for q in range(DEG+1-p)]
rows=[]
for n in range(4,4+int(sys.argv[4])):
  f=[sum(c(n)[l]*w(n-l,i) for l in range(5)) for i in range(n+4)]
  G=[F(0)]
  for x in f: G.append(G[-1]+x)
  for i in range(0,n//2+3):
    s=F(2)**(n-2*i)
    row=[F(n**p*i**q)*C(n-i-a,i-b)*C(n-i-a2,i-b2) for (a,b,a2,b2) in basis for (p,q) in mons]
    rows.append((row,G[i]/s))
ncol=len(basis)*len(mons)
A=[r+[v] for r,v in rows]
piv=[];r=0
for col in range(ncol):
  pr=next((k for k in range(r,len(A)) if A[k][col]!=0),None)
  if pr is None: continue
  A[r],A[pr]=A[pr],A[r]
  inv=1/A[r][col]
  A[r]=[x*inv for x in A[r]]
  for k in range(len(A)):
    if k!=r and A[k][col]!=0:
      fac=A[k][col]; A[k]=[x-fac*y for x,y in zip(A[k],A[r])]
  piv.append(col); r+=1
cons=all(all(x==0 for x in A[k]) for k in range(r,len(A)))
print('DEG',DEG,'AMAX',AMAX,'B',BSET,'cols',ncol,'rows',len(A),'rank',r,'consistent',cons,flush=True)
if cons:
  sol=[F(0)]*ncol
  for k,col in enumerate(piv): sol[col]=A[k][-1]
  for idx,(bb) in enumerate(basis):
    terms=[(str(sol[idx*len(mons)+j]),mons[j]) for j in range(len(mons)) if sol[idx*len(mons)+j]!=0]
    if terms: print(bb,terms)
