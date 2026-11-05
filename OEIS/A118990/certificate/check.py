#!/usr/bin/env python3
# Brute-force check of A118990(n) = 2^n * A086906(n-1).
#
# A118990(n): symmetric singular n x n matrices with entries +1/-1.
# A086906(m): symmetric singular m x m matrices with entries 0/1.
# Counts both by enumeration for n <= 5 (2^15 matrices at the top),
# compares with the OEIS terms, and checks the identity on all OEIS
# terms n = 2..10.
#
import itertools, sys

def det(a):
  # Bareiss fraction-free elimination, exact over the integers.
  #
  a = [row[:] for row in a]
  n, sign, prev = len(a), 1, 1
  for k in range(n - 1):
    if a[k][k] == 0:
      sw = next((r for r in range(k + 1, n) if a[r][k] != 0), None)
      if sw is None:
        return 0
      a[k], a[sw] = a[sw], a[k]
      sign = -sign
    for i in range(k + 1, n):
      for j in range(k + 1, n):
        a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) // prev
    prev = a[k][k]
  return sign * a[n - 1][n - 1] if n else 1

def count_singular_sym(n, vals):
  # Enumerate the entries on and above the diagonal.
  #
  pos = [(i, j) for i in range(n) for j in range(i, n)]
  c = 0
  for v in itertools.product(vals, repeat=len(pos)):
    m = [[0] * n for _ in range(n)]
    for (i, j), x in zip(pos, v):
      m[i][j] = x
      m[j][i] = x
    if det(m) == 0:
      c += 1
  return c

# OEIS terms, offset 1.
#
A118990 = [0, 4, 32, 512, 15872, 907008, 104535552, 22523623424,
           9599255461888, 7747175087620096]
A086906 = [1, 4, 32, 496, 14172, 816684, 87982904, 18748545824,
           7565600671504, 5940152086634096]

ok = True
for n in range(1, 6):
  pm, zo = count_singular_sym(n, (1, -1)), count_singular_sym(n, (0, 1))
  good = (pm == A118990[n - 1]) and (zo == A086906[n - 1])
  ok = ok and good
  print("n=%d  pm=%d  zo=%d  match_oeis=%s" % (n, pm, zo, good))
for n in range(2, 11):
  good = (A118990[n - 1] == (2 ** n) * A086906[n - 2])
  ok = ok and good
  print("A118990(%d) = 2^%d * A086906(%d): %s" % (n, n, n - 1, good))
print("ALL OK" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
