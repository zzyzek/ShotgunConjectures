# A192205: l1 = sum |c_k| of (1-x-x^2+x^3)^n; l2^2 = sum c_k^2 = C(4n,n);
# l1^(1/n) approaches 16/(3 sqrt 3) (slowly, factor (3n+1)^(1/2n)).
#
from math import comb, sqrt
P = [1]
out = []
for n in range(1, 1201):
  Q = [0] * (len(P) + 3)
  for i, c in enumerate(P):
    Q[i] += c; Q[i+1] -= c; Q[i+2] -= c; Q[i+3] += c
  P = Q
  if n < 200: assert sum(c*c for c in P) == comb(4*n, n), n
  if n in (10, 100, 400, 1200):
    l1 = sum(abs(c) for c in P)
    out.append((n, l1 ** (1.0/n) if n < 300 else 2 ** (l1.bit_length() / n)))
print("sum c_k^2 = C(4n,n) for n < 200; limit 16/(3*sqrt3) =", 16/(3*sqrt(3)))
print("a(n)^(1/n) samples:", out)
