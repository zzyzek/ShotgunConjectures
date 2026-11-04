# Deterministic Miller-Rabin for n < 3.3e24 (bases = first 13 primes).
#
def is_prime(n):
  if n < 2: return False
  small = [2,3,5,7,11,13,17,19,23,29,31,37,41]
  for p in small:
    if n % p == 0: return n == p
  d, s = n-1, 0
  while d % 2 == 0: d //= 2; s += 1
  for a in small:
    x = pow(a, d, n)
    if x in (1, n-1): continue
    for _ in range(s-1):
      x = x*x % n
      if x == n-1: break
    else: return False
  return True
