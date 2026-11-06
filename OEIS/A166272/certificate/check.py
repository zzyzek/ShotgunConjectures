# For k in the A166102 b-file: S(k) = sum of 1<=i<=k with J(i,k)=1; check k does not
# divide S, the reduced denominator of S/k is 3, and 3S/k equals A166272 (b-file).
import sys
from fractions import Fraction
from sympy import jacobi_symbol
def read(p):
  d = {}
  for line in open(p):
    t = line.split()
    if len(t) == 2 and not line.startswith('#'): d[int(t[0])] = int(t[1])
  return d
b102 = read(sys.argv[1]); b272 = read(sys.argv[2])
for n, k in sorted(b102.items()):
  S = sum(i for i in range(1, k + 1) if jacobi_symbol(i, k) == 1)
  f = Fraction(S, k)
  assert f.denominator == 3, (n, k)
  if n in b272: assert f.numerator == b272[n] == 3 * S // k, n
print("checked", len(b102), "terms of A166102;", len(b272), "of A166272")
