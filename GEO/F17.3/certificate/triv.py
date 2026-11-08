"""Hoehner-Ledford Lemma 3.10 bound F_N(alpha) for polytopes with a trivalent vertex,
certified upper bound of max over alpha in [0, 4pi] by interval arithmetic (mpmath.iv),
compared with the best known volume V*(N)."""
import sys
from mpmath import iv, mp, mpf
iv.dps = 30

def F(N, a):
  pi = iv.pi
  t1 = iv.tan((2 * pi - a) / 6)
  b = ((4 * N - 18) * pi + a) / (12 * N - 42)
  t2 = iv.tan(b)
  return (iv.sqrt(3) / 4) * (1 - t1**2 / 3) + iv.mpf(2 * N - 7) / 4 * t2 * (1 - t2**2 / 3)

def certify(N, target, pieces):
  hi = None
  four_pi = 4 * iv.pi
  for i in range(pieces):
    a = iv.mpf([ (four_pi * i / pieces).a, (four_pi * (i + 1) / pieces).b ])
    v = F(N, a)
    hi = v.b if hi is None or v.b > hi else hi
  return hi

N = int(sys.argv[1]); target = mpf(sys.argv[2]); pieces = int(sys.argv[3])
ub = certify(N, target, pieces)
print("N", N, "interval upper bound of max F_N:", ub, "target V*", target, "below target:", ub < target)
