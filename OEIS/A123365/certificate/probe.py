# A123365 retry probe.
# 1. c(q^e) closed form (q = 2 mod 3) against brute force.
# 2. Local congruence lemmas for 3c(n) = n + 2.
# 3. Case A (n = pB) for B = q^a r^b, two primes q, r = 2 mod 3, a, b in {2,3,5,6}.
#
from sympy import isprime, primerange, factorint
def cb(n):
  return len({pow(x, 3, n) for x in range(n)})
def cq(q, e):
  return 1 + sum((q - 1)*q**(j - 1) for j in range(e, 0, -3))
def cp(p, e):
  return 1 + sum((p - 1)*p**(j - 1)//3 for j in range(e, 0, -3))
for q in [2, 5, 11]:
  for e in range(1, 7):
    if q**e < 20000: assert cb(q**e) == cq(q, e), (q, e)
for p in [7, 13]:
  for e in range(1, 4):
    assert cb(p**e) == cp(p, e)
# Terms up to N by brute force: only 1 and primes 1 mod 6.
N = 4000
for n in range(1, N):
  if 3*cb(n) == n + 2:
    assert n == 1 or (isprime(n) and n % 6 == 1), n
# Case A two-prime-power search.
qs = [q for q in primerange(5, 3000) if q % 3 == 2]
hits = 0
for i, q in enumerate(qs):
  for r in qs[i + 1:]:
    for a in (2, 3, 5, 6):
      for b in (2, 3, 5, 6):
        B  = q**a * r**b
        c  = cq(q, a)*cq(r, b)
        num, den = 2*(c - 1), B - c
        if num % den == 0:
          p = num//den
          if p % 6 == 1 and isprime(p): hits += 1; print("HIT", p, q, a, r, b)
print("ok; case-A two-prime hits:", hits)
