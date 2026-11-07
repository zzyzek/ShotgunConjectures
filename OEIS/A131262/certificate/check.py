# Checks A130654(k) = v2(A002430(k)/A046990(k)) = min(s2(k)-1, 1+v2(k)) for k <= K,
# computing tan Taylor coefficients from tangent numbers (Seidel triangle), and
# the least k with A130654(k) = n for n <= 5.
import sys
from fractions import Fraction
from math import factorial, gcd
K = int(sys.argv[1]) if len(sys.argv) > 1 else 1100
# tangent numbers via the derivative polynomial recurrence: tan^(n) = P_n(tan), P_{n+1} = (1+x^2) P_n'
# use the boustrophedon (Entringer) triangle to get zigzag numbers E_m; T_k = E_{2k-1}
N = 2*K
row = [1]; E = [1]
for m in range(1, N):
  new = [0]
  for j in range(m):
    new.append(new[-1] + row[m-1-j])
  row = new; E.append(row[-1])
def v2(x):
  c = 0
  while x % 2 == 0: x//=2; c+=1
  return c
first = {}
bad = 0; nonpow2 = 0
for k in range(1, K+1):
  t = Fraction(E[2*k-1], factorial(2*k-1))
  c = t / (2*k)
  r = Fraction(t.numerator, c.numerator)
  assert r.denominator == 1
  r = r.numerator
  a = v2(r)
  if r != 1 << a: nonpow2 += 1
  pred = min(bin(k).count('1') - 1, 1 + v2(k))
  if a != pred: bad += 1; print("mismatch", k, a, pred)
  if a not in first: first[a] = k
print("checked k<=", K, "mismatches", bad, "non-power-of-2 ratios", nonpow2)
print("least k:", sorted(first.items()))
print("formula:", [1] + [4**n - 2**(n-1) for n in range(1, 6)])
