# G(x) = exp( sum_n G(L(n) x)^n x^n/n ) for several Gauss sequences L (exp(sum L x^n/n) integral)
from fractions import Fraction as F
from math import comb
import sys
N=int(sys.argv[1])
def mul(a,b):
  c=[F(0)]*(N+1)
  for i,x in enumerate(a):
    if x:
      for j in range(N+1-i):
        if b[j]: c[i+j]+=x*b[j]
  return c
def exp0(L):
  A=[F(1)]+[F(0)]*N
  for n in range(N):
    A[n+1]=sum((j+1)*L[j+1]*A[n-j] for j in range(n+1))/(n+1)
  return A
def sigma(n): return sum(d for d in range(1,n+1) if n%d==0)
def solve(Lf):
  A=[F(1)]+[F(0)]*N
  for it in range(N+1):
    L=[F(0)]*(N+1)
    for n in range(1,N+1):
      B=[x*F(Lf(n))**i for i,x in enumerate(A)]
      T=[F(1)]+[F(0)]*N
      for _ in range(n): T=mul(T,B)
      for i in range(N+1-n): L[i+n]+=T[i]/n
    A=exp0(L)
  return A
tests={'sigma':sigma,'2^n':lambda n:2**n,'C(2n,n)':lambda n:comb(2*n,n),'3^n-(-2)^n':lambda n:3**n-(-2)**n,'(-1)^n*6':lambda n:6*(-1)**n,
 'NOT gauss: n':lambda n:n+1}
for name,Lf in tests.items():
  A=solve(Lf)
  print(name,'nonint',[n for n in range(N+1) if A[n].denominator!=1][:4],[str(x) for x in A[:8]])
