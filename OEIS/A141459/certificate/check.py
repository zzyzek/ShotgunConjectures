# Checks I_n := int_0^1 log(1-1/x)^n dx = 2^n B'_n (pi i)^n numerically (mpmath, n <= 8),
# den(2^n B'_n) against the A141459 b-file (n <= 300), and the A211163 data terms
# (numerators of (-1/pi^n) I_n = -2^n B'_n i^n, n >= 2).
import sys, os
from fractions import Fraction
from math import comb
N = 300
B = [Fraction(1)]
for m in range(1, N + 1):
  B.append(-sum(comb(m + 1, k) * B[k] for k in range(m)) / (m + 1))
Bp = [b if n != 1 else -b for n, b in enumerate(B)]   # bernoulli' (B'_1 = +1/2)
here = os.path.dirname(os.path.abspath(__file__))
bf = {int(l.split()[0]): int(l.split()[1]) for l in open(os.path.join(here, 'b141459.txt')) if l.strip() and l[0] != '#'}
ok = all((Fraction(2) ** n * Bp[n]).denominator == bf[n] for n in range(N + 1))
print("den(2^n B'_n) = A141459(n), n <= 300:", ok)
A211163 = [2, 0, 8, 0, 32, 0, 128, 0, 2560, 0, 1415168, 0, 57344, 0, 118521856, 0, 5749735424, 0,
           91546451968, 0, 1792043646976, 0, 1982765704675328, 0, 286994513002496, 0,
           3187598700536922112, 0, 4625594563496048066560]
vals = []
for n in range(2, 2 + len(A211163)):
  v = -(Fraction(2) ** n) * Bp[n] * (1 if n % 4 == 0 else -1 if n % 2 == 0 else 0)
  vals.append(v.numerator)
print("numerators of (-1/pi^n) I_n = A211163 data:", vals == A211163)
try:
  import mpmath
  mpmath.mp.dps = 30
  good = True
  for n in range(0, 9):
    I = mpmath.quad(lambda x: mpmath.log(1 - 1 / mpmath.mpf(x) + 0j) ** n, [0, 0.5, 1])
    pred = mpmath.mpf(2) ** n * mpmath.mpf(Bp[n].numerator) / Bp[n].denominator * (mpmath.pi * 1j) ** n
    if abs(I - pred) > mpmath.mpf(10) ** -12 * (1 + abs(pred)): good = False; print("mismatch", n, I, pred)
  print("numerical integral matches 2^n B'_n (pi i)^n, n <= 8:", good)
except ImportError:
  print("mpmath not available")
