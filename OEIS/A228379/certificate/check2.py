from fractions import Fraction
from math import prod, factorial, comb
from sympy import factorint, isprime
def esym(xs):
  c=[1]
  for x in xs:
    c=[ (c[i] if i<len(c) else 0) + (x*c[i-1] if i>=1 else 0) for i in range(len(c)+1)]
  return c
for n in range(2,61):
  xs=[i*i for i in range(n)]
  e=esym(xs)
  S=sum(e[n-m]*e[m]*prod(comb(n,k) for k in range(n+1) if k!=m) for m in range(n+1))
  V2=prod((j*j-i*i)**2 for i in range(n) for j in range(i+1,n))
  D=2*prod(factorial(k)*factorial(2*k-1) for k in range(1,n+1))
  r=Fraction(V2*(2*n-1),D)
  r2=Fraction(V2*S,D)
  if r.denominator!=1 or n<12: print(n, "V2*(2n-1)/D den", factorint(r.denominator), "full ok", r2.denominator==1, "2n-1 prime", isprime(2*n-1), "S mod 2n-1", S%(2*n-1))
print("done")
