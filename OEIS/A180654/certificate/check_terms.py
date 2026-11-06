from fractions import Fraction as F
from math import comb, factorial
N=26
def mul(a,b):
  c=[F(0)]*(N+1)
  for i,x in enumerate(a):
    if x:
      for j in range(N+1-i):
        if b[j]: c[i+j]+=x*b[j]
  return c
def logs(P):
  L=[F(0)]*(N+1)
  for n in range(1,N+1):
    L[n]=(n*P[n]-sum(k*L[k]*P[n-k] for k in range(1,n)))/n
  return L
for pw in [2,3]:
  for n in range(1,9):
    P=[F(comb(n,k)**pw) if k<=n else F(0) for k in range(N+1)]
    L=logs(P)
    g=[x/n for x in L]
    T=[F(1)]+[F(0)]*N
    for _ in range(n): T=mul(T,g)
    t=[T[i]*factorial(i)/factorial(n) for i in range(N+1)]
    bad=[i for i in range(N+1) if t[i].denominator!=1]
    # also: is g = log(P)/n itself Hurwitz? 
    gb=[i for i in range(N+1) if (g[i]*factorial(i)).denominator!=1]
    print(pw,n,'term nonint at',bad[:5],'den',[t[i].denominator for i in bad[:3]],'log/n nonHurwitz',gb[:3])
