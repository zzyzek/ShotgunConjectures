# A223925 conjecture: a(2n) = 4^n divides A132049(2n) = numerator of 4n*e(2n-1)/e(2n), e = A000111
# (Seidel-Entringer triangle, as in the A132049 Maple program). Checks n <= 300: v_2(A132049(2n)) = 2n,
# secant numbers e(2n) odd, v_2(e(2n-1)) = 2n - 2 - v_2(n), and A132049(2n)/4^n odd (Genocchi numbers).
import sys
from fractions import Fraction
N = 600
e = [1]; row = [1]
for n in range(1, N+1):
  new = [0]
  for k in range(1, n+1): new.append(new[-1] + row[n-k])
  row = new; e.append(row[-1])
v2 = lambda x: (x & -x).bit_length() - 1
bad = 0
for n in range(1, N//2 + 1):
  num = Fraction(2*(2*n)*e[2*n-1], e[2*n]).numerator
  if v2(num) != 2*n: bad += 1; print("v2 num", n)
  if e[2*n] % 2 == 0: bad += 1; print("secant even", n)
  if v2(e[2*n-1]) != 2*n - 2 - v2(n): bad += 1; print("tangent v2", n)
print("first quotients A132049(2n)/4^n:", [Fraction(4*n*e[2*n-1], e[2*n]).numerator >> (2*n) for n in range(1, 7)])
print("n <= %d failures:" % (N//2), bad); sys.exit(1 if bad else 0)
