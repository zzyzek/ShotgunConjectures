# Checks for the cube-count part (OEIS-A123365, core-multiplicative-exact-target).
# 1. Closed forms of c(q^e) (number of cubes mod q^e) against brute force.
# 2. (p+2) c(q^e) = p q^e + 2: search over q < 2000, e <= 12, any prime p (finds p = 3, B = 16 only).
# 3. 3c(n) = n + 2 by brute-force cube counts for n < 20000: only n = 1 and primes 1 mod 6.
#
from sympy import isprime, primerange, factorint

def cb(n):
  return len({pow(x, 3, n) for x in range(n)})

def s1(q, e):
  return sum(q**(j - 1) for j in range(1, e + 1) if (j - e) % 3 == 0)

def cq(q, e):
  return 1 + (q - 1)*s1(q, e)

def cp(p, e):
  return 1 + ((p - 1)*s1(p, e))//3

for q in [2, 5, 11, 17, 23]:
  for e in range(1, 9):
    if q**e <= 60000:
      assert cb(q**e) == cq(q, e), (q, e)
for p in [7, 13, 19, 31]:
  for e in range(1, 6):
    if p**e <= 60000:
      assert cb(p**e) == cp(p, e), (p, e)
print("closed forms ok")

hits = []
for q in primerange(2, 2000):
  if q % 3 != 2: continue
  for e in range(1, 13):
    B, c = q**e, cq(q, e)
    if B == c: continue
    if (2*(c - 1)) % (B - c) == 0:
      p = 2*(c - 1)//(B - c)
      if isprime(p): hits.append((p, q, e))
print("prime-power hits (any prime p):", hits)

sols = [n for n in range(1, 20000) if 3*cb(n) == n + 2]
assert all(n == 1 or (isprime(n) and n % 6 == 1) for n in sols)
print("3c(n) = n+2, n < 20000: only 1 and primes 1 mod 6;", len(sols), "solutions")
