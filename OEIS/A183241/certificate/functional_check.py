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
  # exp of series with L[0]=0
  A=[F(1)]+[F(0)]*N
  for n in range(N):
    A[n+1]=sum((j+1)*L[j+1]*A[n-j] for j in range(n+1))/(n+1)
  return A
def scale(A,c): return [x*c**i for i,x in enumerate(A)]
def shift(A,k): return [F(0)]*k+A[:N+1-k]
def pw(A,k):
  r=[F(1)]+[F(0)]*N
  for _ in range(k): r=mul(r,A)
  return r
def solve(step):
  A=[F(1)]+[F(0)]*N
  for it in range(N+1): A=step(A)
  return A
def s157675(A):
  L=[F(0)]*(N+1)
  for n in range(1,N+1):
    t=shift(pw(scale(A,2**n),n),n)
    L=[l+x/n for l,x in zip(L,t)]
  return exp0(L)
def s15690x(q):
  def st(A):
    L=[F(0)]*(N+1)
    for k in range(1,N+1):
      B=scale(A,q**k); B[0]-=1
      t=pw(B,k)
      L=[l+x/k for l,x in zip(L,t)]
    return [F(1)]+shift(exp0(L),1)[1:]
  return st
for name,st in [('A157675',s157675),('A156907',s15690x(2)),('A156908',s15690x(3))]:
  A=solve(st)
  print(name,[n for n in range(N+1) if A[n].denominator!=1][:5],[int(x) for x in A[:7]])
