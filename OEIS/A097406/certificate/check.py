# A097406: every primitive prime factor p of 2^n - 1 has ord_p(2) = n, so p == 1 (mod n);
# for prime n every prime factor of 2^n - 1 is == 1 (mod n).  n <= 90 (sympy factorint).
from sympy import factorint, isprime
ok = True
for n in range(2, 91):
  fs = factorint(2**n - 1)
  prim = [p for p in fs if all((2**m - 1) % p for m in range(1, n))]
  if any(p % n != 1 for p in prim): ok = False
  if isprime(n) and any(p % n != 1 for p in fs): ok = False
print("parts (1) and (3) hold for n <= 90:", ok)
