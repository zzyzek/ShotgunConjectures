"""Independent check of n!(n+q)! | (2n-p)! by Legendre's formula over all primes <= 2n-p."""
import sys
import numpy as np
def primes_upto(m):
  s = np.ones(m + 1, bool); s[:2] = False
  for i in range(2, int(m**0.5) + 1):
    if s[i]: s[i*i::i] = False
  return np.nonzero(s)[0]
def v(a, l):
  t = 0
  while a: a //= l; t += a
  return t
for arg in sys.argv[1:]:
  p, q, n = map(int, arg.split(','))
  ok = all(v(2*n-p, int(l)) >= v(n, int(l)) + v(n+q, int(l)) for l in primes_upto(n + q))
  # primes in (n+q, 2n-p] divide only the numerator
  print(p, q, n, ok)
