"""A054120: geometric definition (sum between vertical lines) vs A081577(n,k) - A081577(n-2,k-1),
and McGarvey's first recurrence, for n < 40. Run: nice -n 19 python3 check.py"""
from functools import lru_cache
import sys
sys.setrecursionlimit(10000)

@lru_cache(None)
def T(n, k):
    if k < 0 or k > n: return 0
    if k == 0 or k == n: return 1
    return sum(T(i, j) for i in range(n) for j in range(i + 1)
               if 2 * k - n - 1 <= 2 * j - i <= 2 * k - n + 1)

@lru_cache(None)
def S(a, b):
    if a == 0 or b == 0: return 1
    return S(a, b - 1) + 2 * S(a - 1, b - 1) + S(a - 1, b)

R = lambda n, k: S(n - k, k) if 0 <= k <= n else 0
data = [1,1,1,1,3,1,1,6,6,1,1,9,18,9,1,1,12,39,39,12,1,1,15,69,114,69,15,1]
assert [T(n, k) for n in range(7) for k in range(n + 1)] == data
for n in range(40):
    for k in range(n + 1):
        assert T(n, k) == R(n, k) - R(n - 2, k - 1)
        assert S(n - k, k) == S(k, n - k)
        if n >= 3 and k >= 1:
            assert T(n, k) == T(n - 1, k - 1) + 2 * T(n - 2, k - 1) + T(n - 1, k)
print("OK")
