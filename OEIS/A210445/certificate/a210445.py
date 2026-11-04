# A210445: least k with k*n practical.  Claim: a(n) < n for n > 1 and
# a(n) < n/2 for n > 47.  Proof sketch in audit/oeis-b.jsonl; this script
# does the finite part: every prime 47 < p < 2881 has a practical k < p/2
# with k*p practical, and checks the family argument numerically above.
#
from sympy import factorint, primerange, divisor_sigma

def practical(m):
  if m == 1: return True
  if m % 2: return False
  s = 1
  for p, e in sorted(factorint(m).items()):
    if p > s + 1: return False
    s *= (p**(e + 1) - 1) // (p - 1)
  return True

def a(n):
  k = 1
  while not practical(k * n): k += 1
  return k

bad = []
for n in range(2, 6001):
  v = a(n)
  if (v >= n) or ((n > 47) and (2 * v >= n)): bad.append((n, v))
print('n in [2,6000] violating a(n)<n or (n>47 and a(n)<n/2):', bad)

# Family check: for x = p-1 >= 2880 the least sigma(k) >= x over
# k in {2^a*105, 2^a*165 : a >= 3} gives k < x/2.
#
fam = sorted([(int(divisor_sigma(2**a * m)), 2**a * m) for a in range(3, 60) for m in (105, 165)])
worst = 0.0
for p in primerange(2881, 2 * 10**6):
  x = p - 1
  for s, k in fam:
    if s >= x: break
  assert practical(k) and practical(k * p)
  worst = max(worst, k / x)
print('family argument, primes 2881..2e6: max k/(p-1) =', worst)
