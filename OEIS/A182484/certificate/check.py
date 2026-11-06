from fractions import Fraction
from math import isqrt
def val(p):
    r=Fraction(1)
    for k in range(1,p):
        r*=Fraction(k)**(2*k-p-1)
    return r
def issq(x):
    if x.denominator!=1: return False
    n=x.numerator; return isqrt(n)**2==n
from sympy import isprime
out=[]
for p in range(2,400):
    s=issq(val(p))
    if s!=isprime(p): out.append((p,s,isprime(p)))
print(out)
