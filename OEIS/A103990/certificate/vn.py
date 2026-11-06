# The recursion that the Lean file uses: Vn(tau,k,l) = V(t^-tau X^k W^l).
from fractions import Fraction as Fr
from functools import lru_cache
from math import comb
from canon import canon, val0
import sys
sys.setrecursionlimit(100000)
@lru_cache(None)
def cc(t): return Fr(1) if t==0 else -2*cc(t-1)/(2*t-1)
@lru_cache(None)
def Vn(t,k,l):
  if l==0: return cc(t)*k**t
  if t==0: return Fr(2**l*l)
  return (2*k*Vn(t-1,k,l)-2*l*Vn(t,k+1,l-1))/(1-2*t-l)
def S(n): return -sum(comb(n,i)*comb(i,m)*(-1)**(i+m)*Vn(i+1,m,n-i) for i in range(n+1) for m in range(i+1))
for n in range(1,41): assert S(n)==Fr(2,3)*Fr(n**3-n**2+2*n+1,2*n+1),n
# Vn agrees with the canonical reduction on monomials t^-tau X^k W^l
for t in range(0,4):
  for k in range(0,4):
    for l in range(0,4):
      if t==0 and k==0 and l<=1: continue
      v=val0(canon({(-2*t-l,k,l,l-1):Fr(1)})).get(0,Fr(0))
      assert v==Vn(t,k,l),(t,k,l,v,Vn(t,k,l))
print("Vn recursion: S(n) = formula for n<=40; Vn = canonical value on t^-tau X^k W^l (tau,k,l<=3)")
