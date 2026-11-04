# A094787: a(n) = least prime p with p + n a perfect power.  For each prime q < 5000
# find m > q with no perfect power in [m^2 - q + 2, m^2 - 1]; then a(m^2 - q) = q.
# Verifies a(m^2 - q) = q directly.
#
from sympy import primerange, integer_nthroot
def ispp(x):
  if x < 4: return x == 1
  for k in range(2, x.bit_length() + 1):
    r, ex = integer_nthroot(x, k)
    if ex: return True
  return False
def a(n):
  for p in primerange(2, 10**9):
    if ispp(p + n): return p
ok = True; ex = {}
for q in primerange(2, 5000):
  m = q + 1
  while any(ispp(x) for x in range(m*m - q + 2, m*m)): m += 1
  if a(m*m - q) != q: ok = False
  ex[q] = m
print("all primes < 5000 occur:", ok, " sample m:", {q: ex[q] for q in list(ex)[:8]})
