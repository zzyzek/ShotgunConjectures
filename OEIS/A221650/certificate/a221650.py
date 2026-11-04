# A221650: number of partitions of n with at least m parts equal to k
# (equivalently, with an m-th part of size k) equals p(n - m k); n <= 30.
#
from functools import lru_cache
def parts(n, mx=None):
  if mx is None: mx = n
  if n == 0: yield (); return
  for f in range(min(n, mx), 0, -1):
    for r in parts(n - f, f): yield (f,) + r
@lru_cache(None)
def p(n): return sum(1 for _ in parts(n)) if n >= 0 else 0
ok = True
for n in range(0, 31):
  P = list(parts(n))
  for k in range(1, n + 1):
    for m in range(1, n // k + 1):
      ok &= (sum(1 for q in P if q.count(k) >= m) == p(n - m * k))
print("count(partitions of n with >= m parts k) = p(n - mk) for n <= 30:", ok)
