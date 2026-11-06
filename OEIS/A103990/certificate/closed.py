# Closed forms used in the Lean file, checked against the recursions:
#   I(al,be) = int_0^1 r^(al+be) (r-2)^al dr
#   a(t,l) = T(t,l,t):  a(0,0)=1, a(0,l)=l 2^l, a(t,l) = (-1)^t l 2^l - 2^(l+1) t I(t-1,l)  (t>=1)
#   q(t,l) = (-1)^t 2^l (-l(2l+3t)/6) + 2^l (l^2 - 2lt - 5l - 3t^2 - 3t)/3 I(t,l)
from fractions import Fraction as Fr
from math import comb, factorial
from functools import lru_cache
from ab import A, B
def I(al,be): return sum(Fr(comb(al,c)*(-2)**(al-c),al+be+c+1) for c in range(al+1))
def aE(t,l):
  if t==0: return Fr(1) if l==0 else Fr(l*2**l)
  return (-1)**t*l*2**l - 2**(l+1)*t*I(t-1,l)
def qE(t,l): return (-1)**t*2**l*Fr(-l*(2*l+3*t),6) + 2**l*Fr(l*l-2*l*t-5*l-3*t*t-3*t,3)*I(t,l)
for t in range(0,9):
  for l in range(0,9):
    assert aE(t,l)==factorial(t)*A(t,l),(t,l)
    assert qE(t,l)==factorial(t)*(B(t+1,l)+comb(t+1,2)*A(t+1,l)),(t,l)
print("closed forms of a and q agree with the recursions for t,l <= 8")
for n in range(1,60):
  s=sum(comb(n,i)*qE(i,n-i) for i in range(n+1))
  assert -s==Fr(2,3)*Fr(n**3-n**2+2*n+1,2*n+1)
print("diagonal sums ok n<60")
