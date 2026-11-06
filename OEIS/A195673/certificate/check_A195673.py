# Recompute A195673 from its recurrence, compare with the OEIS data, and
# check the conjecture p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x) (A053119)
# for a grid of (p, q) and n <= 30.
#
from math import comb

def T(p, q, N):
  rows = [[p], [q, 0]]
  for n in range(2, N+1):
    rows.append([ (rows[n-1][k] if k <= n-1 else 0) -
                  (rows[n-2][k-2] if 0 <= k-2 <= n-2 else 0) for k in range(n+1) ])
  return rows

data = [-2,3,0,3,0,2,3,0,-1,0,3,0,-4,0,-2,3,0,-7,0,-1,0,3,0,-10,0,3,0,2,3,0,
        -13,0,10,0,3,0,3,0,-16,0,20,0,0,0,-2,3,0,-19,0,33,0,-10,0,-5,0,3,0,
        -22,0,49,0,-30,0,-5,0,2,3,0,-25,0,68]
flat = [x for r in T(-2, 3, 12) for x in r]
assert flat[:len(data)] == data, "data mismatch"

def S(n, k):
  return ((-1)**(k//2) * comb(n - k//2, k//2)) if (k % 2 == 0 and k <= n) else 0

for p in range(-5, 6):
  for q in range(-5, 6):
    a, b = T(p+1, q+1, 30), T(p, q, 30)
    for n in range(31):
      for k in range(n+1):
        assert a[n][k] - b[n][k] == S(n, k), (p, q, n, k)
print("OK: data (%d terms) and conjecture for p,q in [-5,5], n <= 30" % len(data))
