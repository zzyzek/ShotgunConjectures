# a(n) = n - a(a(a(a(a(n-1))))), a(0) = 0 (OEIS A005376); compare with c*n,
# c the real root of x^5 + x - 1 (= 1/plastic number). Prints max |a(n) - c n| on dyadic ranges.
import math
N = 2 * 10 ** 6
a = [0] * (N + 1)
for n in range(1, N + 1):
    m = a[n - 1]
    for _ in range(4): m = a[m]
    a[n] = n - m
lo, hi = 0.0, 1.0
for _ in range(200):
    mid = (lo + hi) / 2
    if mid ** 5 + mid - 1 < 0: lo = mid
    else: hi = mid
c = lo
print('c =', c)
print('a(0..20) =', a[:21])
k = 1
while 2 ** k <= N:
    e = max(abs(a[n] - c * n) for n in range(2 ** (k - 1), 2 ** k + 1))
    print('n in [2^%d, 2^%d]: max |a(n) - c n| = %.3f' % (k - 1, k, e))
    k += 1
