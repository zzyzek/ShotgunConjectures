# A088617 check: T(n,k) = C(n+k,n) C(n,k)/(k+1) counts Schroeder n-paths with
# k U steps (brute force, n <= 9), the identities used in
# A088617_mathlib.lean, and the mean number of U steps divided by n.
#
# Usage: python3 check.py
#
from math import comb, sqrt
from fractions import Fraction

NMAX = 800

def T(n, k):
  if (k < 0) or (k > n):
    return 0
  return comb(n + k, n) * comb(n, k) // (k + 1)

# Schroeder paths of semilength n by number of U steps: walk over steps
# U = (1,1), D = (1,-1), H = (2,0) from (0,0) to (2n,0), never below 0.
#
def paths_by_u(n):
  cnt = {}
  def go(x, y, u):
    if x == 2 * n:
      if y == 0:
        cnt[u] = cnt.get(u, 0) + 1
      return
    if y > (2 * n - x):
      return
    go(x + 1, y + 1, u + 1)
    if y > 0:
      go(x + 1, y - 1, u)
    if x + 2 <= 2 * n:
      go(x + 2, y, u)
  go(0, 0, 0)
  return cnt

ok = True
for n in range(0, 10):
  c = paths_by_u(n)
  ok = ok and all(c.get(k, 0) == T(n, k) for k in range(0, n + 1))
print("T(n,k) = #Schroeder n-paths with k U steps, n <= 9:", ok)

# Exact division (k+1) | C(n+k,n) C(n,k) and the coefficient identity T_rec.
#
ok = all((comb(n + k, n) * comb(n, k)) % (k + 1) == 0
         for n in range(0, 80) for k in range(0, n + 1))
ok = ok and all((n + 3) * T(n + 2, k + 1) ==
                (2 * n + 3) * (T(n + 1, k + 1) + 2 * T(n + 1, k)) - n * T(n, k + 1)
                for n in range(0, 80) for k in range(0, 85))
print("divisibility and T_rec, n < 80:", ok)

r = [sum(T(n, k) for k in range(0, n + 1)) for n in range(0, NMAX + 1)]
U = [sum(k * T(n, k) for k in range(0, n + 1)) for n in range(0, NMAX + 1)]

ok = all(4 * U[n + 1] == (3 * n + 2) * r[n + 1] - n * r[n] for n in range(0, NMAX))
ok = ok and all((n + 3) * r[n + 2] == 3 * (2 * n + 3) * r[n + 1] - n * r[n]
                for n in range(0, NMAX - 1))
print("4 U(n+1) = (3n+2) r(n+1) - n r(n) and r recurrence, n <", NMAX, ":", ok)

# x(n) = r(n+1)/r(n): the Lean invariant 2 <= x <= 3+2 sqrt2 and
# (n+1)(3+2 sqrt2 - x) <= 20, checked with exact rationals against a
# rational upper bound of 3 + 2 sqrt 2 (and a lower bound for the last test).
#
alo = Fraction(3) + 2 * Fraction(141421356237, 10 ** 11)
ahi = Fraction(3) + 2 * Fraction(141421356238, 10 ** 11)
ok  = True
for n in range(0, 400):
  x  = Fraction(r[n + 1], r[n])
  ok = ok and (2 <= x) and (x <= alo) and ((n + 1) * (ahi - x) <= 20)
print("x(n) invariant, n < 400:", ok)

for n in (10, 100, NMAX):
  print(n, "mean/n =", float(Fraction(U[n], r[n] * n)), "target", sqrt(0.5))
