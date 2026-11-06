# Step 3/4 certificate.  V(t^-tau X^k W^l) (value at 0 of the canonical form of
# t^-tau e^{-k u^2} W^l, t = u^2, W = sqrt(pi) erf(u)/u) is a polynomial in k of
# degree <= tau whose top coefficients A, B obey
#   (1-2tau-l) A(tau,l) = 2A(tau-1,l) - 2l A(tau,l-1)
#   (1-2tau-l) B(tau,l) = 2B(tau-1,l) - 2l (B(tau,l-1) + tau A(tau,l-1))
# A(tau,0) = (-2)^tau/(2tau-1)!!, A(0,l) = 2^l l (l>=1), A(0,0)=1, B(tau,0)=B(0,l)=0;
# and S_n = -sum_i C(n,i) i! (B(i+1,n-i) + C(i+1,2) A(i+1,n-i)).
#
import sys
from fractions import Fraction as Fr
from math import comb, factorial
from canon import canon, val0
from ab import A, B
def V(tau,k,l):
  v=val0(canon({(-2*tau-l,k,l,l-1):Fr(1)}))
  assert set(v)<={0}; return v.get(0,Fr(0))
def fit(vals):
  # Newton forward differences -> monomial coefficients via exact solve
  n=len(vals); import itertools
  M=[[Fr(k)**e for e in range(n)] for k in range(n)]
  # gaussian elimination
  a=[row[:]+[vals[i]] for i,row in enumerate(M)]
  for c in range(n):
    p=next(r for r in range(c,n) if a[r][c]!=0); a[c],a[p]=a[p],a[c]
    for r in range(n):
      if r!=c and a[r][c]!=0:
        f=a[r][c]/a[c][c]; a[r]=[x-f*y for x,y in zip(a[r],a[c])]
  return [a[i][n]/a[i][i] for i in range(n)]
for tau in range(1,5):
  for l in range(0,5):
    vals=[V(tau,k,l) for k in range(tau+3)]
    co=fit(vals)
    assert all(c==0 for c in co[tau+1:]),(tau,l,co)
    assert co[tau]==A(tau,l) and co[tau-1]==B(tau,l),(tau,l,co,A(tau,l),B(tau,l))
print("polynomial degree and top coefficients confirmed for tau<=4, l<=4 (k = 0..tau+2)")
N=int(sys.argv[1]) if len(sys.argv)>1 else 300
for n in range(1,N+1):
  S=-sum(comb(n,i)*factorial(i)*(B(i+1,n-i)+comb(i+1,2)*A(i+1,n-i)) for i in range(n+1))
  assert S==Fr(2,3)*Fr(n**3-n**2+2*n+1,2*n+1),n
print("S_n from the A,B recursion equals the formula for n <=",N)
