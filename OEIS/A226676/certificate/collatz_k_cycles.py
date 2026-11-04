# Explicit primitive cycles for the 3x+k / 3x-k maps of A226661, A226677,
# A226676 (T(x) = x/2 for even x, (3x+-k)/2 for odd x, k odd, gcd(k,6)=1).
#   A226661 (3x+k, exactly n odd elements): L = n+m with m prime, m > 3^n/2
#     and 2^L > 3^n; k = 2^L - 3^n, x0 = 3^n - 2^n.  (Here the smallest
#     m >= 1 with 2^(n+m) > 3^n and gcd(3^n-2^n, 2^m-1) = 1 is used.)
#   A226677 (3x-k, exactly n odd elements, n >= 2): k = 3^n - 2^(n+1), x0 = 3^n - 2^n.
#   A226676 (3x-k, cycle of N elements, N >= 3): n = N-1 odd elements,
#     k = 3^n - 2^N, x0 = 3^n - 2^n.
# Each cycle is simulated and its odd count, length, and primitivity
# (gcd of the elements = 1) are checked.
#
from math import gcd

def cycle(x0, k, sign):
  xs, x = [], x0
  while True:
    xs.append(x)
    x = x // 2 if x % 2 == 0 else (3 * x + sign * k) // 2
    if x == x0: return xs
    if len(xs) > 10**6: return None

def check(x0, k, sign):
  assert k > 0 and k % 2 and k % 3
  c = cycle(x0, k, sign)
  g = 0
  for v in c: g = gcd(g, v)
  return len(c), sum(v % 2 for v in c), g, min(c) > 0

ok = True
for n in range(1, 41):
  m = 1
  while (2**(n + m) <= 3**n) or (gcd(3**n - 2**n, 2**m - 1) != 1): m += 1
  L, odd, g, pos = check(3**n - 2**n, 2**(n + m) - 3**n, 1)
  ok &= (odd == n) and (g == 1) and pos
  if n >= 2:
    L, odd, g, pos = check(3**n - 2**n, 3**n - 2**(n + 1), -1)
    ok &= (odd == n) and (g == 1) and pos
  N = n + 2
  L, odd, g, pos = check(3**(N - 1) - 2**(N - 1), 3**(N - 1) - 2**N, -1)
  ok &= (L == N) and (g == 1) and pos
print('all constructions valid for n = 1..40 (A226676: N = 3..42):', ok)
