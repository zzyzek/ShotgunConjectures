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
def solve(q):
  A=[F(1)]+[F(0)]*N
  for it in range(N+1):
    L=[F(0)]*(N+1)
    for n in range(1,N+1):
      B=[x*F(1,q**n)**i for i,x in enumerate(A)]
      T=[F(1)]+[F(0)]*N
      for _ in range(n): T=mul(T,B)
      for i in range(N+1-n): L[i+n]+=T[i]/n
    A=exp0(L)
  return A
for q in [2,3,4,5,6,8,9,10,12]:
  A=solve(q)
  a=[A[n]*q**(n*(n-1)//2) for n in range(N+1)]
  print(q,'nonint',[n for n in range(N+1) if a[n].denominator!=1][:5],'not1modq',[n for n in range(N+1) if a[n].denominator==1 and a[n]%q!=1][:5],[str(x) for x in a[:7]])
