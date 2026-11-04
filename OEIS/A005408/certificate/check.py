# A005408 / A216371 coach conjecture. Coach of odd b: top row
# 1 = a0, a1, ... with a_{i+1} = odd part of (b - a_i), until it returns to 1.
# A216371 = primes with exactly one coach (the cycle of 1 covers every odd
# residue coprime to b below b/2). b = 4q +- 1.
# Claim: b in A216371  <=>  top row of the coach of 1 is a permutation of 1,3,...,2q-1.
# Checks every odd b, 3 <= b < 2*10^4.
#
def odd(n):
  while n % 2 == 0: n //= 2
  return n

def isprime(n):
  if n < 2: return False
  i = 2
  while i * i <= n:
    if n % i == 0: return False
    i += 1
  return True

from math import gcd
bad = []
for b in range(3, 20000, 2):
  q = (b + 1) // 4 if b % 4 == 3 else (b - 1) // 4
  row, a = [1], odd(b - 1)
  while a != 1: row.append(a); a = odd(b - a)
  rhs = sorted(row) == list(range(1, 2*q, 2))
  ncoprime = sum(1 for x in range(1, (b + 1)//2, 2) if gcd(x, b) == 1)
  lhs = isprime(b) and len(row) == ncoprime
  if lhs != rhs: bad.append(b)
print("mismatches:", bad)
