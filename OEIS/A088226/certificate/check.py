# OEIS A088226: a(1)=0, a(2)=0, a(3)=1, a(n) = |a(n-1) - a(n-2) - a(n-3)|.
# Checks (1) the 105 printed terms, (2) a(n) = f(n-1) for 1 <= n <= N, where
# f(m) = (smallest even |m - s^2|)/2, (3) the literal a(n) = f(n) fails (first n),
# (4) the block formula a(k^2+j) = (j-1)/2 (j odd), k-(j-2)/2 (j even), 1<=j<=2k+1.
#
import math, sys
DATA = [0,0,1,1,0,2,1,1,2,0,3,1,2,2,1,3,0,4,1,3,2,2,3,1,4,0,5,1,4,2,3,3,2,4,
1,5,0,6,1,5,2,4,3,3,4,2,5,1,6,0,7,1,6,2,5,3,4,4,3,5,2,6,1,7,0,8,1,7,
2,6,3,5,4,4,5,3,6,2,7,1,8,0,9,1,8,2,7,3,6,4,5,5,4,6,3,7,2,8,1,9,0,10,1,9,2]
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300000
a = [None, 0, 0, 1]
for n in range(4, N + 1):
  a.append(abs(a[n-1] - a[n-2] - a[n-3]))
assert a[1:len(DATA)+1] == DATA

def f(m):
  # Scan all squares up to (sqrt(m)+2)^2; distances beyond are larger.
  #
  best = None
  for s in range(0, math.isqrt(m) + 3):
    d = abs(m - s*s)
    if d % 2 == 0 and (best is None or d < best): best = d
  return best // 2

assert all(a[n] == f(n-1) for n in range(1, N + 1))
bad = [n for n in range(1, 50) if a[n] != f(n)]
print("literal a(n)=f(n) fails at n =", bad[:8])
for k in range(0, math.isqrt(N) - 1):
  for j in range(1, 2*k + 2):
    g = (j-1)//2 if j % 2 == 1 else k - (j-2)//2
    assert a[k*k + j] == g
print("OK: data", len(DATA), "terms; a(n) = f(n-1) for 1 <= n <=", N)
