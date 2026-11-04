# A098016: (prime(x) + prime(x+1))/2 is never prime (it lies strictly between consecutive primes).
from sympy import primerange, isprime
P = list(primerange(2, 10**6))
print(all((p + q) % 2 or not isprime((p + q) // 2) for p, q in zip(P, P[1:])))
