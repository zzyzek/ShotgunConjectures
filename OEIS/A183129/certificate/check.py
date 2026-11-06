# Hanna binomial-power series exp(sum_n [sum_k base(n,k)^e(n,k) x^k] x^n/n):
# integrality of the series and Gauss congruences of beta_w(j) = j*l_{jw}.
from fractions import Fraction as F
from math import comb, gcd
fams={
 'A183129':(2,lambda n,k:k*k+k),'A183128':(2,lambda n,k:k*k+1),
 'A181084':(1,lambda n,k:n+k+1),'A181082':(1,lambda n,k:n+k),'A181080':(1,lambda n,k:n-k+1),
 'A181078':(2,lambda n,k:n+k-1),'A181076':(2,lambda n,k:n),'A181074':(2,lambda n,k:k+1),
 'A181070':(1,lambda n,k:k+1),
 'bad181070':(1,lambda n,k:k),'bad181074':(2,lambda n,k:k),'bad183128':(2,lambda n,k:k*k),'bad181080':(1,lambda n,k:n-k)}
def base(t,n,k):
  if t==1: return comb(n,k) if k<=n else 0
  return comb(n+k-1,k)
N=24
primes=[2,3,5,7,11,13]
for name,(t,e) in fams.items():
  L=[F(0)]*(N+1)
  for n in range(1,N+1):
    for k in range(0,(min(N-n,n) if t==1 else N-n)+1):
      L[n+k]+=F(base(t,n,k)**e(n,k),n)
  A=[F(1)]+[F(0)]*N
  for n in range(N):
    A[n+1]=sum((j+1)*L[j+1]*A[n-j] for j in range(n+1))/(n+1)
  nonint=[n for n in range(N+1) if A[n].denominator!=1]
  # Gauss check of beta_w
  bad=[]
  for n0 in range(1,7):
    for k0 in range(0,7):
      if gcd(n0,k0)!=1 or (t==1 and k0>n0): continue
      beta=lambda j:F(base(t,j*n0,j*k0)**e(j*n0,j*k0),n0)
      for p in primes:
        for a in (1,2,3):
          for m in (1,2,3):
            if m*p**a>40: continue
            d=beta(m*p**a)-beta(m*p**(a-1))
            if d.denominator!=1 or d.numerator%(p**a): bad.append((n0,k0,p,a,m))
      if any(beta(j).denominator!=1 for j in range(1,8)): bad.append((n0,k0,'nonint'))
  print(name,'series nonint',nonint[:4],'gauss bad',bad[:3],[int(x) if x.denominator==1 else str(x) for x in A[:8]])
