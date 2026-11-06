"""A007669 = A034343: number of binary linear codes of length n (any
dimension) with no zero column, up to permutation of coordinates.

Enumerates every subspace of GF(2)^n by reduced row echelon form, keeps
those with no zero coordinate, and counts S_n-orbits by Burnside's lemma
(one permutation per cycle type, weighted by class size). Also evaluates
Kotesovec's formula for A178717 and compares a(n) with A178717(n-1) - 1.
Usage: python3 burnside.py [nmax]   (nmax <= 9; n = 9 takes a few minutes)
"""
import sys
from itertools import product
from math import factorial, gcd
from collections import Counter


def partitions(n, m=None):
  m = n if m is None else m
  if n == 0:
    yield []
    return
  for k in range(min(n, m), 0, -1):
    for p in partitions(n - k, k):
      yield [k] + p


def class_size(lam, n):
  c = Counter(lam)
  d = 1
  for k, e in c.items():
    d *= (k ** e) * factorial(e)
  return factorial(n) // d


def perm_of(lam):
  p, s = [], 0
  for k in lam:
    p += [s + (i + 1) % k for i in range(k)]
    s += k
  return p


def subspaces(n):
  """Yield (basis list, span bitmask over 2^n vectors) for every subspace."""
  for k in range(n + 1):
    for piv in combos(n, k):
      free = [(r, c) for r in range(k) for c in range(n)
              if c > piv[r] and c not in piv]
      for bits in product((0, 1), repeat=len(free)):
        rows = [1 << piv[r] for r in range(k)]
        for (r, c), b in zip(free, bits):
          if b:
            rows[r] |= 1 << c
        span = {0}
        for v in rows:
          span |= {x ^ v for x in span}
        yield rows, span


def combos(n, k, start=0):
  if k == 0:
    yield []
    return
  for i in range(start, n):
    for c in combos(n, k - 1, i + 1):
      yield [i] + c


def a(n):
  perms = [(class_size(l, n), perm_of(l)) for l in partitions(n)]
  tables = []
  for w, p in perms:
    t = [0] * (1 << n)
    for v in range(1 << n):
      u = 0
      for i in range(n):
        if v >> i & 1:
          u |= 1 << p[i]
      t[v] = u
    tables.append((w, t))
  full = (1 << n) - 1
  tot = 0
  for rows, span in subspaces(n):
    supp = 0
    for v in rows:
      supp |= v
    if supp != full:
      continue
    for w, t in tables:
      if all(t[v] in span for v in rows):
        tot += w
  assert tot % factorial(n) == 0
  return tot // factorial(n)


def phi(m):
  return sum(1 for i in range(1, m + 1) if gcd(i, m) == 1)


def fib(m):
  x, y = 0, 1
  for _ in range(m):
    x, y = y, x + y
  return x


def a178717(k):
  if k == 1:
    return 3
  return 2 * k + 1 + sum(2 * j * phi(i) for j in range(1, k)
                         for i in range(fib(k - j) + 1, fib(k - j + 1) + 1))


nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
data = [1, 2, 4, 8, 16, 36, 80, 194, 506, 1449, 4631, 17106]
print("A178717(1..20):", [a178717(k) for k in range(1, 21)])
for n in range(1, nmax + 1):
  v = a(n)
  rhs = a178717(n - 1) - 1 if n >= 2 else None
  print(n, v, "data", data[n - 1], "A178717(n-1)-1 =", rhs)
  assert v == data[n - 1]
print("OK")
