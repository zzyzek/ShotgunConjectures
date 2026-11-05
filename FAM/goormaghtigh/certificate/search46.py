#!/usr/bin/env python3
# Pair (m, n) = (4, 6): search x^3 + x^2 + x + 1 = y^5 + y^4 + y^3 + y^2 + y + 1
# for 2 <= y <= YMAX (x is the integer cube root neighbourhood of the right side).
# Also report the leading form x^3 - y^5 (irreducible, one place at infinity),
# the reason Runge's squeeze does not apply.
#
import sys

YMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6

def icbrt(n):
  x = int(round(n ** (1.0 / 3)))
  while x ** 3 > n:
    x -= 1
  while (x + 1) ** 3 <= n:
    x += 1
  return x

hits = []
for y in range(2, YMAX + 1):
  r = y**5 + y**4 + y**3 + y**2 + y + 1
  x0 = icbrt(r)
  for x in (x0 - 1, x0, x0 + 1):
    if ( (x > y) and
         ((x**3 + x**2 + x + 1) == r) ):
      hits.append((x, y))
print("YMAX", YMAX, "solutions", hits)
