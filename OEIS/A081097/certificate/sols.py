# A081097 family: n with m n^2 = n + floor(sqrt(m) n floor(sqrt(m) n)),
# exact integer arithmetic.  For each non-square m, list the solutions found
# by searching the Pell-type equation (m n - 1)^2 - m k^2 = c, |c| small,
# k = floor(sqrt(m) n) (every solution has this form, see README), and
# print the ratio pattern of consecutive solutions.
from math import isqrt
import sys
def ok(m, n):
    k = isqrt(m * n * n)
    return m * n * n == n + isqrt(m * n * n * k * k)
LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
for m in [2, 3, 5, 6, 7, 8, 10, 11]:
    s = [n for n in range(1, LIM) if ok(m, n)]
    print(m, s[:14])
