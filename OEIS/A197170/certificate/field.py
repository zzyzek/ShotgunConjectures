# Reading R2 (field unit of Q(sqrt k), as the entry's examples use): k = n^2 * d0, d0 = n^4 v^2 + 2 squarefree,
# v odd, gcd(v, n) = 1. Field unit (A^2+1) + A sqrt(d0), A = n^2 v = (A^2+1) + n v sqrt(k): y = n v, gcd(k, y) = n.
# For each n <= NMAX find the least such v; for n <= 12 confirm the unit by brute force (least y with
# x^2 - d0 y^2 = +-1 or +-4).
import sys
from math import gcd, isqrt
from sympy import factorint
NMAX=int(sys.argv[1])
def sqf(m): return all(e==1 for e in factorint(m).values())
mx=0
for n in range(1,NMAX+1):
  v=1
  while not (v%2==1 and gcd(v,n)==1 and sqf(n**4*v*v+2)): v+=1
  mx=max(mx,v)
  d0=n**4*v*v+2; A=n*n*v; k=n*n*d0
  assert (A*A+1)**2-d0*A*A==1 and gcd(k,n*v)==n
  if n<=12:
    for y in range(1,A+1):
      t=[d0*y*y+s for s in (1,-1,4,-4)]
      if any(u>0 and isqrt(u)**2==u for u in t): break
    assert y==A,(n,y,A)
print("ok n<=",NMAX,"max v",mx)
