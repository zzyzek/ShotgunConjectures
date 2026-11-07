# Greedy A177431: b(n) = least integer > b(n-1) such that the x^n coefficient of exp(sum b(k)^2 x^k/k)
# is an integer (coefficients from n A_n = sum_{k=1..n} b(k)^2 A_{n-k}). Compare with the OEIS data,
# then test Gauss congruences (integrality) of b^m for m = -2..8 on the computed terms.
from fractions import Fraction
data = [1,3,4,5,6,12,13,15,22,28,32,34,38,39,51,55,67,72,75,80,88,96,114,126]
N = 24
b = [0]; A = [Fraction(1)]
for n in range(1, N + 1):
  c = b[-1] + 1 if n > 1 else 1
  while True:
    An = sum(Fraction(b[k]**2) * A[n-k] for k in range(1, n)) + c*c * A[0]
    An /= n
    if An.denominator == 1: break
    c += 1
  b.append(c); A.append(An)
print("greedy:", b[1:]); print("matches data:", b[1:] == data[:N])
def integral(m, upto):
  A = [Fraction(1)]
  for n in range(1, upto + 1):
    A.append(sum(Fraction(b[k])**m * A[n-k] for k in range(1, n + 1)) / n)
    if A[-1].denominator != 1: return n
  return None
for m in range(-2, 9): print("m =", m, "first non-integral coefficient index:", integral(m, N))
