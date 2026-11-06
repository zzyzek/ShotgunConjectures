# D_t(m) = lcm of denominators of coefficients of Q^(t)_{m-1}(n), Q_0 = 1,
# Q_m(n) = sum_{i=1..n} i^t Q_{m-1}(i). Generalized binomials C^(t)(n,m) = n!^(t)/(m!^(t)(n-m)!^(t)),
# n!^(t) = D_t(n+1).
from fractions import Fraction
from math import comb, lcm
import sys
MAXK=700
B=[Fraction(1)]
for n in range(1,MAXK+2):
  B.append(-sum(comb(n+1,j)*B[j] for j in range(n))/ (n+1))
# S_k(n) = sum_{i=1}^n i^k, as coefficient list (index = power), using B_1 = +1/2 convention
def S(k):
  c=[Fraction(0)]*(k+2)
  for j in range(k+1):
    bj = B[j] if j!=1 else Fraction(1,2)
    c[k+1-j]+=Fraction(comb(k+1,j))*bj/(k+1)
  return c
Sc={}
def Sk(k):
  if k not in Sc: Sc[k]=S(k)
  return Sc[k]
def D(t,M):
  Q=[Fraction(1)]; out=[1]
  for m in range(1,M):
    new=[Fraction(0)]*(len(Q)+t+1)
    for j,c in enumerate(Q):
      if c:
        s=Sk(t+j)
        for e,v in enumerate(s): new[e]+=c*v
    Q=new
    d=1
    for c in Q: d=lcm(d,c.denominator)
    out.append(d)
  return out
if __name__=="__main__":
  t=int(sys.argv[1]); M=int(sys.argv[2])
  print(D(t,M)[:10])
