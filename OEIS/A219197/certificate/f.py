# Check a(n) = [t^n] sqrt((1-3t)/(1+t)) (1-t)^(-2n-2) exactly, and the mod-4 formula
# a(n) = C(3n+1,n) + 2 sum_{1<=m<=n, v2(m) even} C(3n+1-m, n-m) (mod 4).
from math import comb
from fractions import Fraction
N=300
# exact a(n) via A002426 formula from the entry
def T(k): return sum(comb(k,2*j)*comb(2*j,j) for j in range(k//2+1))
Tk=[T(k) for k in range(N+1)]
def a(n):
  if n==0: return 1
  s=sum(Fraction(Tk[k]*comb(3*n-k+1,n-k)*(2*k+1),3*n-k+1) for k in range(n+1))
  assert s.denominator==1; return s.numerator
def v2(m):
  c=0
  while m%2==0: m//=2; c+=1
  return c
# series sqrt((1-3t)/(1+t)) to order N, exact rationals -> integers? coefficients are integers? check
# compute via sqrt(1-4u), u=t/(1+t): sqrt(1-4u) = 1 - 2 sum_{k>=1} Cat(k-1) u^k
cat=[comb(2*k,k)//(k+1) for k in range(N+1)]
# u^k coefficients
S=[0]*(N+1); S[0]=1
u=[0]*(N+1); u[1]=1
for i in range(2,N+1): u[i]=-u[i-1]   # t/(1+t) = t - t^2 + ...
uk=[1]+[0]*N
for k in range(1,N+1):
  new=[0]*(N+1)
  for i in range(N+1):
    if uk[i]:
      for j in range(1,N+1-i): new[i+j]+=uk[i]*u[j]
  uk=new
  for i in range(N+1): S[i]-=2*cat[k-1]*uk[i]
bad1=bad2=0
for n in range(0,121):
  an=a(n)
  e=sum(S[m]*comb(2*n+1+(n-m),n-m) for m in range(n+1))
  if e!=an: bad1+=1
  f=(comb(3*n+1,n)+2*sum(comb(3*n+1-m,n-m) for m in range(1,n+1) if v2(m)%2==0))%4
  if f!=an%4: bad2+=1
print("exact Lagrange formula mismatches:",bad1," mod-4 formula mismatches:",bad2)
