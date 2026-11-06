from fractions import Fraction as F
from math import comb, factorial
import sys
N=int(sys.argv[1])
def mul(a,b):
  c=[F(0)]*(N+1)
  for i,x in enumerate(a):
    if x:
      for j in range(N+1-i):
        if b[j]: c[i+j]+=x*b[j]
  return c
def log1p(P):
  # log of P with P[0]=1
  L=[F(0)]*(N+1)
  # L' = P'/P : n L_n = n P_n - sum_{k=1}^{n-1} k L_k P_{n-k}
  for n in range(1,N+1):
    L[n]=(n*P[n]-sum(k*L[k]*P[n-k] for k in range(1,n)))/n
  return L
for pw in [1,2,3,'n']:
  A=[F(1)]+[F(0)]*N
  for n in range(1,N//2+1):
    e = n if pw=='n' else pw
    P=[F(comb(n,k)**e) if k<=n else F(0) for k in range(N+1)]
    L=log1p(P)
    T=[F(1)]+[F(0)]*N
    for _ in range(n): T=mul(T,L)
    c=F(1,factorial(n)*n**n)
    for i in range(N+1-n):
      A[i+n]+=T[i]*c
  a=[A[i]*factorial(i) for i in range(N+1)]
  print(pw,'nonint',[i for i in range(N+1) if a[i].denominator!=1][:8],[str(x) for x in a[:10]])
