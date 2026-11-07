# Checks the circulant/Ramanujan-sum closed forms for A228884, A228885
# against direct determinants, and the A228379 Cauchy-Binet formula.
from sympy import Matrix, gcd, totient, divisors, mobius, binomial, factorint
from itertools import combinations
from math import prod
def a884(n): return Matrix(n,n,lambda i,j: gcd(i-j,n)).det() if n else 1
def a885(n): return Matrix(n,n,lambda i,j: 1 if gcd(i+j+2,n)==1 else 0).det() if n else 1
def f884(n):
  return prod(sum(e*totient(n//e) for e in divisors(gcd(k,n))) for k in range(n))
def f885(n):
  # det of circulant = prod Ramanujan sums; times sign of j->-j
  c=lambda k: mobius(n//gcd(n,k))*totient(n)//totient(n//gcd(n,k))
  return (-1)**((n-1)//2)*prod(c(k) for k in range(n))
for n in range(1,31):
  assert a884(n)==f884(n),n
  assert a885(n)==f885(n),n
print("884/885 ok to 30")
from sympy import symbols
def a379(n): return Matrix(n,n,lambda i,j:(i*i+j*j)**n).det()
def e(m,xs): return sum(prod(c) for c in combinations(xs,m))
def f379(n):
  xs=[i*i for i in range(n)]
  V=prod(xs[j]-xs[i] for i in range(n) for j in range(i+1,n))
  S=sum(e(n-m,xs)*e(m,xs)*prod(binomial(n,k) for k in range(n+1) if k!=m) for m in range(n+1))
  return (-1)**(n*(n-1)//2)*V*V*S, S
from sympy import factorial
for n in range(1,10):
  v,S=f379(n); assert v==a379(n),n
  D=2*prod(factorial(k)*factorial(2*k-1) for k in range(1,n+1))
  V=prod((j*j-i*i) for i in range(n) for j in range(i+1,n))
  print(n, v%D==0, factorint(D), factorint(V*V) if n>1 else 1)
