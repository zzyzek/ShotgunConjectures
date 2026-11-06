from fractions import Fraction as F
from math import factorial, gcd
import sys
sys.setrecursionlimit(10000)
def expser(b,N):
  A=[F(1)]+[F(0)]*N
  for n in range(N):
    A[n+1]=sum(F(b[j+1])*A[n-j] for j in range(n+1))/(n+1)
  return A
def partitions(n,mx=None):
  if mx is None: mx=n
  if n==0: yield []; return
  for k in range(min(n,mx),0,-1):
    for p in partitions(n-k,k): yield [k]+p
def multsum(n,r):
  s=0
  for p in partitions(n):
    m=factorial(n)
    for x in p: m//=factorial(x)
    s+=m**r
  return s
def gauss(b,N):
  bad=[]
  for n in range(2,N+1):
    for p in [q for q in range(2,n+1) if all(q%d for d in range(2,q)) and n%q==0]:
      a=0; m=n
      while m%p==0: m//=p; a+=1
      for e in range(1,a+1):
        if (b[m*p**e]-b[m*p**(e-1)])%(p**e): bad.append((n,p,e))
  return bad
N=int(sys.argv[1])
for r in (2,3):
  b=[0]+[multsum(n,r) for n in range(1,N+1)]
  A=expser(b,N)
  print('r',r,'nonint',[n for n in range(N+1) if A[n].denominator!=1][:10],'gaussbad',gauss(b,N)[:10], [int(x) for x in A[:8]])
