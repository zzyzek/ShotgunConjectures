# (1) The canonical integration-by-parts reduction (canon.py) reproduces the four
#     integrands I_1..I_4 printed on MathWorld's "Hypercube Line Picking" page exactly.
# (2) sqrt(pi) I_n(0) reproduces the 20 terms of A103990/A103991.
# (3) sqrt(pi) I_n(0) = (2/3)(n^3-n^2+2n+1)/(2n+1) for n <= N (argument).
# Terms: (a,k,l,p) -> c means c * pi^(p/2) * x^a * e^{-k x^2} * erf(x)^l.
#
import sys
from fractions import Fraction as Fr
from canon import canon, start, val0
F=Fr
MW={1:{(0,1,0,-1):F(2,3)},
 2:{(-1,1,1,0):F(1,3),(0,2,0,-1):F(4,15),(0,1,0,-1):F(4,15)},
 3:{(0,1,2,1):F(-2,5),(-1,2,1,0):F(4,5),(-1,1,1,0):F(1,5),(0,3,0,-1):F(-12,35),(0,2,0,-1):F(68,105),(0,1,0,-1):F(8,105)},
 4:{(-1,1,3,2):F(-2,15),(0,2,2,1):F(-136,105),(0,1,2,1):F(-32,105),(-1,3,1,0):F(197,210),(-1,2,1,0):F(104,105),
    (-1,1,1,0):F(1,14),(0,4,0,-1):F(-676,945),(0,3,0,-1):F(16,35),(0,2,0,-1):F(146,315),(0,1,0,-1):F(16,945)}}
for n in range(1,5):
  T=canon(start(n)); assert T==MW[n],(n,T)
print("I_1..I_4 equal MathWorld's integrands")
num=[2,6,50,38,74,386,206,310,1334,614,822,3218,1370,1718,6362,2582,3106,11090,4358,5094]
den=[3,5,21,9,11,39,15,17,57,21,23,75,27,29,93,33,35,111,39,41]
N=int(sys.argv[1]) if len(sys.argv)>1 else 25
for n in range(1,N+1):
  v=val0(canon(start(n))); assert set(v)<={0}; v=v[0]
  if n<=20: assert (v.numerator,v.denominator)==(num[n-1],den[n-1]),n
  assert v==Fr(2,3)*Fr(n**3-n**2+2*n+1,2*n+1),n
print("OEIS terms n=1..20 reproduced; formula holds for n <=",N)
