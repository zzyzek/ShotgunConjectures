from fractions import Fraction as Fr
from math import comb, factorial
from functools import lru_cache
def df(m):
  r=1
  for i in range(m,0,-2): r*=i
  return r
@lru_cache(None)
def A(t,l):
  if l==0: return Fr((-2)**t, df(2*t-1))
  if t==0: return Fr(2**l*l)
  return (2*A(t-1,l)-2*l*A(t,l-1))/(1-2*t-l)
@lru_cache(None)
def B(t,l):
  if l==0 or t==0: return Fr(0)
  return (2*B(t-1,l)-2*l*(B(t,l-1)+t*A(t,l-1)))/(1-2*t-l)
if __name__=="__main__":
  for n in range(1,15):
    S=-sum(comb(n,i)*factorial(i)*(B(i+1,n-i)+comb(i+1,2)*A(i+1,n-i)) for i in range(n+1))
    print(n,S)
