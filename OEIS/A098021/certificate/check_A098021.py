"""A098021: compare the former definition (second difference of frac(n sqrt 2), 60-digit
decimals) with the current one (exact, floor(m sqrt 2) = isqrt(2 m^2)) for n < 20000,
and check the listed terms and a(n) = 3n + 2 floor(n sqrt 2).
"""
from decimal import Decimal, getcontext
from math import isqrt

getcontext().prec = 60
R = Decimal(2).sqrt()
DATA = [5, 10, 17, 22, 29, 34, 39, 46, 51, 58, 63, 68, 75, 80, 87]


def fl(x):
  return int(x.to_integral_value(rounding="ROUND_FLOOR"))


def fr(x):
  return x - fl(x)


def g(x):
  if x <= Decimal(1) / 3:
    return -1
  if x <= Decimal(2) / 3:
    return 0
  return 1


def old(n):
  f0, f1, f2 = fr(n * R), fr((n + 1) * R), fr((n + 2) * R)
  return abs((f2 - 2 * f1 + f0) - g(f1)) < Decimal(10) ** -40


def new(n):
  # floor(n r + 2 r) - floor(n r) - 2, with floor(m sqrt 2) = isqrt(2 m^2)
  #
  return isqrt(2 * (n + 2) ** 2) - isqrt(2 * n * n) - 2 == 0


def main():
  N = 20000
  seq = []
  for n in range(1, N):
    o, w = old(n), new(n)
    assert o == w, n
    if w:
      seq.append(n)
  assert seq[:len(DATA)] == DATA
  for i, v in enumerate(seq, 1):
    assert v == 3 * i + 2 * isqrt(2 * i * i)
  print("A098021: old == new for 1 <= n < %d; %d terms match 3n+2floor(n sqrt2)" % (N, len(seq)))


main()
