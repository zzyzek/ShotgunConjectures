# Checks for OEIS A202150 / A202146 (parity of the q-series analog of pi/2).
# 1. A(x) = sum_n x^n (x;x)_n/(x;x^2)_{n+1} (the A202146 g.f.) to degree D,
#    compared with the OEIS b-file b202146.txt if present (pass its path as argv[1]).
# 2. Identity (*): sum_n (-x)^n (-x;x)_n/(x;x^2)_{n+1} = sum_m (-1)^m x^{3m(m+1)} to degree D.
# 3. A(x) mod 2 has odd coefficients exactly at 3m(m+1), degree <= D.
# 4. Finite identities E_1(n) = (-q;q)_n and E_3(n) = q^n (-q;q)_n, n <= 12, where
#    E_b(n) = sum_j (-1)^j q^(3j^2+bj) [2n+1, n-2j]_q.
import sys
D = 1500
def series(sign):
  # sum_n s^n x^n (s x; x)_n / (x; x^2)_{n+1}, s = +1 gives (x;x)_n with x^n,
  # s = -1 gives (-x)^n (-x;x)_n
  S = [0] * (D + 1)
  c = [0] * (D + 1); c[0] = 1
  # c = (s x;x)_n / (x;x^2)_{n+1}; start n = 0: 1/(1-x)
  for i in range(1, D + 1): c[i] += c[i - 1]
  for n in range(0, D + 1):
    if n > 0:
      # multiply by (1 - s x^n) where (sx;x)_n uses factor (1 - s x^n) ... with s=+1 -> (1 - x^n)
      for i in range(D, n - 1, -1): c[i] -= sign * c[i - n]
      m = 2 * n + 1
      for i in range(m, D + 1): c[i] += c[i - m]
    f = sign ** n
    for i in range(0, D + 1 - n): S[i + n] += f * c[i]
  return S
A = series(1)
B = series(-1)
theta = [0] * (D + 1)
m = 0
while 3 * m * (m + 1) <= D:
  theta[3 * m * (m + 1)] += (-1) ** m; m += 1
assert B == theta, "identity (*) fails"
odd = {3 * m * (m + 1) for m in range(0, 40)}
assert all(((A[i] % 2) == 1) == (i in odd) for i in range(D + 1)), "parity fails"
print("identity (*) and parity hold to degree", D)
print("A202146 first terms:", A[:20])
print("A202150:", [A[3 * k * (k + 1)] for k in range(0, 22) if 3 * k * (k + 1) <= D])
if len(sys.argv) > 1:
  bf = {}
  for line in open(sys.argv[1]):
    p = line.split()
    if len(p) == 2 and not line.startswith('#'): bf[int(p[0])] = int(p[1])
  assert all(A[k] == v for k, v in bf.items() if k <= D), "b-file mismatch"
  print("b-file agrees for", len([k for k in bf if k <= D]), "terms")
# 4. finite identities
import sympy as sp
q = sp.symbols('q')
def qbin(N, k):
  if k < 0 or k > N: return sp.Integer(0)
  num = sp.Integer(1); den = sp.Integer(1)
  for i in range(k): num *= (1 - q**(N - i)); den *= (1 - q**(i + 1))
  return sp.cancel(num / den)
def E(b, n):
  return sp.expand(sum((-1)**j * q**(3*j*j + b*j) * qbin(2*n + 1, n - 2*j) for j in range(-n - 1, n + 2)))
for n in range(0, 13):
  P = sp.Integer(1)
  for k in range(1, n + 1): P *= (1 + q**k)
  assert sp.expand(E(1, n) - P) == 0 and sp.expand(E(3, n) - q**n * P) == 0, n
print("finite identities E_1, E_3 hold for n <= 12")
