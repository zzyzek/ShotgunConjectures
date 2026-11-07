# For 4 <= n <= 150 find the least n-gonal N (index m >= 2) that is not k-gonal for 3 <= k < n.
# n = 6 has none (every hexagonal number is triangular); searched up to index 2000 there.
from math import isqrt
def is_poly(k, N):
  # N = P_k(m) iff 8(k-2)N + (k-4)^2 = X^2 with X = 2(k-2)m - (k-4), m >= 0
  D = 8*(k-2)*N + (k-4)**2; X = isqrt(D)
  return X*X == D and (X + (k-4)) % (2*(k-2)) == 0
for n in range(4, 151):
  found = None
  for m in range(2, 2001):
    N = m*((n-2)*m - n + 4)//2
    if not any(is_poly(k, N) for k in range(3, n)):
      found = N; break
  if (found is None) != (n == 6): print("unexpected", n, found)
  if n <= 30: print(n, found)
print("done")
