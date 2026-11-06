# A(x) = exp( sum_n (q^n + A(x))^n x^n/n ), integer q
from fractions import Fraction as F
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
for q in [-3,-2,-1,0,1,2,3,5,6]:
  A=[F(1)]+[F(0)]*N
  for it in range(N+1):
    L=[F(0)]*(N+1)
    for n in range(1,N+1):
      B=A[:]; B[0]+=q**n
      T=[F(1)]+[F(0)]*N
      for _ in range(n): T=mul(T,B)
      for i in range(N+1-n): L[i+n]+=T[i]/n
    A=exp0(L)
  print(q,'nonint',[n for n in range(N+1) if A[n].denominator!=1][:4],[str(x) for x in A[:8]])
