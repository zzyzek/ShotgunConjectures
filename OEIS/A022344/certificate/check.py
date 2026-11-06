# Wythoff array rows (n >= 1): row n starts floor(floor(n*phi)*phi), floor(floor(n*phi)*phi^2).
# Check: characteristic of row n (0-indexed n-1) equals A022344(n-1); for random pairs of rows
# and j, |F3| is eventually a row with characteristic a(n)a(m) (found by searching the array).
from decimal import Decimal, getcontext
import math, random
getcontext().prec = 60
phi = (1 + Decimal(5).sqrt()) / 2
def lw(n): return int((n * phi).to_integral_value(rounding='ROUND_FLOOR'))
def row(n, L=40):
  x = int((lw(n) * phi).to_integral_value(rounding='ROUND_FLOOR'))
  y = int((lw(n) * phi * phi).to_integral_value(rounding='ROUND_FLOOR'))
  r = [x, y]
  while len(r) < L: r.append(r[-1] + r[-2])
  return r
def A022344(n):
  f = lw(n + 1); return f * f - n * f - n * n
N = 300
rows = {n: row(n) for n in range(1, N + 1)}
where = {}
for n, r in rows.items():
  for k, v in enumerate(r[:25]): where[v] = (n, k)
for n in range(1, N + 1):
  r = rows[n]; c = abs(r[1] ** 2 - r[0] * r[2])
  assert c == A022344(n - 1), n
random.seed(1); tested = 0
for _ in range(300):
  n, m, j = random.randint(1, 30), random.randint(1, 30), random.randint(0, 5)
  F1, F2 = rows[n], rows[m]
  F3 = [F1[i] * F2[j + 1] - F1[i + 1] * F2[j] for i in range(30)]
  G = [abs(t) for t in F3]
  i0 = 20
  assert all(t > 0 for t in F3[i0:]) or all(t < 0 for t in F3[i0:])
  # find the row containing G[i0], G[i0+1] consecutively
  if G[i0] in where:
    rr, k = where[G[i0]]
    if rows[rr][k + 1] == G[i0 + 1]:
      assert A022344(rr - 1) == A022344(n - 1) * A022344(m - 1)
      tested += 1
# Cases where the needed entry lies outside the 300 x 25 table are skipped.
print("rows 1..%d: characteristic = A022344(n-1); product rule confirmed in %d random cases" % (N, tested))
