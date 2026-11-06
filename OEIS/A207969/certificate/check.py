# Coefficients of exp(sum_{n>=1} 5 F(n)^(2k) x^n/n) by the recurrence
# n a_n = sum_{j=1..n} b_j a_{n-j}; checks integrality for k <= 6, n <= 80, and
# compares k = 2, 3 with the OEIS data of A207969 and A207970.
from fractions import Fraction
def fib(n):
  a, b = 0, 1
  for _ in range(n): a, b = b, a + b
  return a
def coeffs(k, N):
  b = [5 * fib(n) ** (2 * k) for n in range(N + 1)]
  a = [Fraction(1)]
  for n in range(1, N + 1):
    a.append(sum(b[j] * a[n - j] for j in range(1, n + 1)) / n)
  return a
ok = True
for k in range(7):
  a = coeffs(k, 80)
  if any(x.denominator != 1 for x in a): ok = False; print("non-integral", k)
A207969 = [1, 5, 15, 60, 295, 1625, 9430]
A207970 = [1, 5, 15, 140, 1505, 21875, 319620]
print("integral k<=6, n<=80:", ok)
print("A207969 data:", [int(x) for x in coeffs(2, 6)] == A207969)
print("A207970 data:", [int(x) for x in coeffs(3, 6)] == A207970)
