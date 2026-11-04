# A090519: some prime p in (10^n/4, 10^n/2] gives floor(10^n/p) in {2, 3}.
# Checks n = 2..30 with the least prime above 10^n/4 (sympy nextprime).
#
from sympy import nextprime, isprime
print(all(isprime(10**n // nextprime(10**n // 4)) and nextprime(10**n // 4) <= 10**n // 2 for n in range(2, 31)))
print("a(1): floor(10/2) = 5 prime:", isprime(10 // 2))
