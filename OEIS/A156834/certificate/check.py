from math import comb, gcd
from sympy import totient, mobius, divisors, isprime
def T156348(n,k): return comb(n//k-2+k,k-1) if n%k==0 else 0
def mu54525(n,k): return mobius(n//k) if n%k==0 else 0
def a834(n): return sum(T156348(n,k)*totient(k) for k in range(1,n+1))
def a833(n): return sum(mu54525(n,j)*T156348(j,k)*k for j in range(1,n+1) for k in range(1,j+1))
d834=[1,2,3,5,5,12,7,17,19,30,11,63,13,56,99,89,17,154,19,269,237,132,23,509,301,182,379,783,29,1230,31,881,813,306,2125,2431,37,380,1299,4157,41,4822,43,3695,6175,552,47,8529,5587,6266,2787]
d833=[1,2,3,6,5,16,7,24,24,38,11,103,13,68,127,144,17,261,19,404,291,152,23,994,370,206,540,1093,29,2195,31,1584,943,338,2543,4808,37,416,1479,7371,41,7929,43,4691,8976,596,47,18876,6510,11035,3091]
assert [a834(n) for n in range(1,52)]==d834
assert [a833(n) for n in range(1,52)]==d833
for n in range(2,400):
    A=a834(n); B=a833(n)
    assert (A==n)==isprime(n) and (B==n)==isprime(n) and A>=n and B>=n
print("ok")
