# General form: P_n in 1+xZ[x] with n | k [x^k]P_n  =>  sum_n (log P_n)^n/(n! n^n) is Hurwitz-integral.
import random
from fractions import Fraction as F
from math import factorial
random.seed(1)
N=18
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
for trial in range(3):
  A=[F(1)]+[F(0)]*N
  for n in range(1,N+1):
    P=[F(1)]+[F(0)]*N
    for k in range(1,min(n,6)+1):
      from math import gcd
      P[k]=F(random.randint(-9,9)*(n//gcd(n,k)))
    g=[x/n for x in logs(P)]
    T=[F(1)]+[F(0)]*N
    for _ in range(n): T=mul(T,g)
    for i in range(N+1): A[i]+=T[i]/factorial(n)
  print('trial',trial,'nonint',[i for i in range(N+1) if (A[i]*factorial(i)).denominator!=1])
