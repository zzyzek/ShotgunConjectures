# A210826: a(n) defined by the Lambert series sum a(n) x^n/(1-x^n) = sum x^(n^3),
# i.e. sum_{d|n} a(d) = [n is a cube]; compare with the multiplicative formula
# a(p^e) = -1 + ((e+2) mod 3) for n <= 20000.
#
from sympy import factorint, divisors
N = 20000
cube = lambda n: round(n ** (1/3)) ** 3 == n or (round(n ** (1/3)) + 1) ** 3 == n or (round(n ** (1/3)) - 1) ** 3 == n
a = [0] * (N + 1)
for n in range(1, N + 1):
  a[n] = int(cube(n)) - sum(a[d] for d in divisors(n)[:-1])
def m(n):
  r = 1
  for p, e in factorint(n).items(): r *= -1 + ((e + 2) % 3)
  return r
print("Lambert coefficients equal the multiplicative formula for n <= %d:" % N, all(a[n] == m(n) for n in range(1, N + 1)))
