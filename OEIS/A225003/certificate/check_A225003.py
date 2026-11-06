"""A225003: floor(1/frac(e^(5/(7n)))) against the listed terms and floor((7n-3)/5),
and A047332 (residues 0,2,3,5,6 mod 7) against floor((7n-3)/5)."""
from decimal import Decimal, getcontext

getcontext().prec = 80
DATA = [23, 2, 3, 5, 6, 7, 9, 10, 12, 13, 14, 16, 17, 19, 20, 21, 23, 24, 26, 27, 28, 30,
        31, 33, 34, 35, 37, 38, 40, 41, 42, 44, 45, 47, 48, 49, 51, 52, 54, 55, 56, 58, 59,
        61, 62, 63, 65, 66, 68, 69, 70, 72, 73, 75, 76, 77, 79, 80, 82, 83, 84, 86, 87, 89,
        90, 91, 93]


def a(n):
  x = (Decimal(5) / (7 * n)).exp()
  f = x - int(x)
  return int(1 / f)


def main():
  N = 5000
  A047332 = [m for m in range(10 * N) if m % 7 in (0, 2, 3, 5, 6)][:N]
  for n in range(1, N + 1):
    v = a(n)
    if n <= len(DATA):
      assert v == DATA[n - 1], n
    if n >= 2:
      assert v == (7 * n - 3) // 5 == A047332[n - 1], n
  print("A225003: data match; a(n) = floor((7n-3)/5) = A047332(n) for 2 <= n <= %d" % N)


main()
