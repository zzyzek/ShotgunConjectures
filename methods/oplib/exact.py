"""
Exact integer arithmetic for statements written with reals.

Pattern. Conjectures like "floor(C(n,4)^(1/4)) = floor((n - 3/2)/24^(1/4))" or
"least m with n! <= m^m" are decided with integers only: replace each floor of
a k-th root or a quotient of radicals by the integer inequality that defines
it. Floating point gets these wrong exactly at the interesting n.

Used for: OEIS-A100682 (counterexamples near continued-fraction convergents
of 384^(1/4)), A214449 vs A118168 (n! vs m^m).
"""
from math import isqrt


def iroot(x, k):
  """floor(x^(1/k)) for integer x >= 0."""
  if x < 2:
    return x
  r = int(round(x ** (1.0 / k))) if x < (1 << 1000) else 1 << ((x.bit_length() + k - 1) // k)
  while r ** k > x:
    r -= 1
  while (r + 1) ** k <= x:
    r += 1
  return r


def floor_ratio_root(num, den, c, k):
  """floor( (num/den) / c^(1/k) ) for positive integers, num/den >= 0.
  b <= (num/den)/c^(1/k)  <=>  c * (b*den)^k <= num^k."""
  b = iroot(num ** k // (c * den ** k), k)
  while c * ((b + 1) * den) ** k <= num ** k:
    b += 1
  while (b > 0) and (c * (b * den) ** k > num ** k):
    b -= 1
  return b


def least_m_power_ge(N):
  """Least m >= 1 with m^m >= N."""
  lo, hi = 1, 2
  while hi ** hi < N:
    hi *= 2
  while lo < hi:
    mid = (lo + hi) // 2
    if mid ** mid >= N:
      hi = mid
    else:
      lo = mid + 1
  return lo


def nearest_power_base(N):
  """argmin_m |m^m - N| over m >= 1 (ties: smaller m)."""
  m = least_m_power_ge(N)
  cands = [x for x in (m - 1, m) if x >= 1]
  return min(cands, key=lambda x: (abs(x ** x - N), x))
