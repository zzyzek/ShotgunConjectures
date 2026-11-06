# a(n) = coefficients of B(x)^(1/3), B = sum C(n+2,2) 2^(n(n-1)) x^n, by exact recursion
# a_n = (b_n - [x^n](sum_{i<n} a_i x^i)^3) / 3 (Fractions); checks integrality, a(n) = 1 mod 3,
# the parity pattern (odd iff n has no 1-bit at an even position >= 2) for n <= N,
# and the OEIS b-file (pass its path).
import sys
from fractions import Fraction
N = 200
b = [((n + 1) * (n + 2) // 2) * 2 ** (n * (n - 1)) for n in range(N + 1)]
a = [Fraction(1)]
sq = [Fraction(1)]            # square of the current truncation, kept to degree N
for n in range(1, N + 1):
  # cube coefficient n of truncation sum_{i<n} a_i x^i
  c = sum(a[i] * sum(a[j] * a[n - i - j] for j in range(0, n - i + 1) if j < n and n - i - j < n)
          for i in range(0, n))
  a.append((b[n] - c) / 3)
for n, x in enumerate(a):
  assert x.denominator == 1, n
  assert x.numerator % 3 == 1, n
def odd_claim(n):
  return all(((n >> k) & 1) == 0 for k in range(2, n.bit_length() + 1, 2))
assert all((a[n].numerator % 2 == 1) == odd_claim(n) for n in range(N + 1))
print("integral, = 1 mod 3, parity claim OK for n <=", N)
if len(sys.argv) > 1:
  for line in open(sys.argv[1]):
    t = line.split()
    if len(t) == 2 and not line.startswith('#'):
      assert a[int(t[0])] == int(t[1]), t
  print("b-file agrees")
