# OEIS A195538 / A195539 (Pythagorean approximations b(n)/a(n) to sqrt(8)).
# Definition (Moses' Mathematica program in the entries): s = r + sqrt(1 + r^2) with r = sqrt(8),
# i.e. s = 3 + 2 sqrt(2); p/q = n-th convergent of the regular continued fraction of s (n terms);
# b(n)/a(n) = (p^2 - q^2)/(2 p q) in lowest terms.
# Checks the printed terms, Mathar's recurrences and the bisections, with the bisection
# sequences computed from their own OEIS definitions:
#   A098602(n) = A001652(n) A046090(n); A001652: x(n) = 6x(n-1) - x(n-2) + 2, x(0)=0, x(1)=3;
#   A046090: X+1 over Pythagorean triples (X, X+1, Z) by increasing Z (brute force);
#   A076218: numbers m with 2m^2 - 3m + 1 a square (brute force over the Pell solutions' range);
#   A046176: m such that m^2 is hexagonal; A000129 Pell numbers.
#
from fractions import Fraction
from math import isqrt, gcd
import sys
A = [5,12,145,420,4901,14280,166465,485112,5654885,16479540,192099601,
     559819260,6525731525,19017375312,221682772225,646030941360]
B = [12,35,408,1189,13860,40391,470832,1372105,15994428,46611179,
     543339720,1583407981,18457556052,53789260175,627013566048]
N = int(sys.argv[1]) if len(sys.argv) > 1 else 60

# Exact CF of 3 + 2 sqrt 2: x = (P + Q sqrt 2)/R, floor via integer sqrt.
#
def cf_terms(n):
  P, Q, R, out = 3, 2, 1, []
  for _ in range(n):
    # floor((P + Q sqrt2)/R) with Q >= 0, R > 0
    #
    def le(c):
      # c <= (P + Q sqrt2)/R  <=>  Q sqrt2 >= c R - P = d  (R > 0)
      #
      d = c*R - P
      if Q >= 0: return d <= 0 or 2*Q*Q >= d*d
      return d < 0 and 2*Q*Q <= d*d
    t = (P + (isqrt(2*Q*Q) if Q >= 0 else -isqrt(2*Q*Q))) // R
    while not le(t): t -= 1
    while le(t+1): t += 1
    out.append(t)
    # x - t = (P - tR + Q sqrt2)/R; invert: R/(P' + Q sqrt2) = R(P' - Q sqrt2)/(P'^2 - 2Q^2)
    #
    Pp = P - t*R
    den = Pp*Pp - 2*Q*Q
    P, Q, R = R*Pp, -R*Q, den
    if R < 0: P, Q, R = -P, -Q, -R
    g = gcd(gcd(abs(P), abs(Q)), R)
    P, Q, R = P // g, Q // g, R // g
  return out

T = cf_terms(N + 1)
assert T[0] == 5 and all(T[i] == (1 if i % 2 else 4) for i in range(1, N + 1))
a, b = [None], [None]
pm, p, qm, q = 1, T[0], 0, 1
for n in range(1, N + 1):
  if n > 1:
    pm, p, qm, q = p, T[n-1]*p + pm, q, T[n-1]*q + qm
  fr = Fraction(p*p - q*q, 2*p*q)
  a.append(fr.denominator); b.append(fr.numerator)
assert a[1:len(A)+1] == A and b[1:len(B)+1] == B
for n in range(7, N + 1): assert a[n] == 35*a[n-2] - 35*a[n-4] + a[n-6]
for n in range(5, N + 1): assert b[n] == 34*b[n-2] - b[n-4]

pell = [0, 1]
while len(pell) < 2*N + 10: pell.append(2*pell[-1] + pell[-2])
x = [0, 3]
while len(x) < N: x.append(6*x[-1] - x[-2] + 2)
# A046090 by brute force over X up to x[8] (Pythagorean (X, X+1, Z)).
#
LIM = x[7] + 1
pyX = [X for X in range(0, LIM) if isqrt(X*X + (X+1)**2)**2 == X*X + (X+1)**2]
assert pyX == x[:len(pyX)] and len(pyX) == 8
A046090 = [X + 1 for X in x]
A098602 = [x[i] * A046090[i] for i in range(len(x))]
# A076218 by brute force up to a bound, then the Pell form y^2+1 for larger terms.
#
small = [m for m in range(0, 10**6) if isqrt(2*m*m - 3*m + 1)**2 == 2*m*m - 3*m + 1]
A076218 = [None] + small
hexidx = [m for m in range(1, 10**6) if any(h*(2*h-1) == m*m for h in [ (1 + isqrt(1 + 8*m*m)) // 4 ])]
A046176 = [None] + hexidx
for k in range(1, N//2 + 1):
  assert a[2*k] == A098602[k]
  if k + 2 < len(A076218): assert a[2*k-1] == A076218[k+2]
for n in range(0, (N-1)//2 + 1):
  assert b[2*n+1] == pell[4*n+4]
for n in range(1, N//2 + 1):
  if n + 1 < len(A046176): assert b[2*n] == A046176[n+1]
print("OK: CF [5;1,4,1,4,...]; data; recurrences for n <=", N, "; bisections (brute-force ranges:",
      len(small), "A076218 terms,", len(hexidx), "A046176 terms)")
