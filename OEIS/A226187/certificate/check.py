# A226187(n) = least k with H_k > n/3 (exact rationals).
# Prints a(1..40) and the ratios a(n+1)/a(n) against exp(1/3).
#
from fractions import Fraction
import math

M = 40
a = []
H = Fraction(0)
k = 0
for n in range(1, M + 1):
  t = Fraction(n, 3)
  while not (H > t):
    k += 1
    H += Fraction(1, k)
  a.append(k)

print("a(1..40):", a)
assert a[9] == 16, a[9]
for n in (10, 20, 30, 39):
  print(n, a[n] / a[n - 1], math.exp(1 / 3))
