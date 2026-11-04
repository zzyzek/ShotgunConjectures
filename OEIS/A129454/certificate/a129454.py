# A129454: a(n) = prod_{i,j,k=1..n-1} gcd(i,j,k) (offset 0).  Compare v_p(a(n))
# with the conjectured sum_t floor(n/p^t)^3 and with sum_t floor((n-1)/p^t)^3.
#
from math import gcd
def a(n):
  r = 1
  for i in range(1, n):
    for j in range(1, n):
      g = gcd(i, j)
      for k in range(1, n): r *= gcd(g, k)
  return r
def v(x, p):
  e = 0
  while x % p == 0: x //= p; e += 1
  return e
def form(N, p):
  s, q = 0, p
  while q <= N: s += (N // q) ** 3; q *= p
  return s
lit_bad = []
for n in range(0, 25):
  x = a(n)
  for p in (2, 3, 5, 7, 11, 13, 17, 19, 23):
    assert v(x, p) == form(n - 1, p) if n >= 1 else True, (n, p)
    if v(x, p) != form(n, p): lit_bad.append((n, p))
print("shifted formula sum floor((n-1)/p^t)^3 holds for n <= 24")
print("literal formula fails, first cases (n, p):", lit_bad[:6])
