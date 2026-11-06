# For N = 2n+1: S(N) = sum_{i<=N} i*J(i,N), A166406(n) = -S(N), A166100(n) = sum_{J=+1} i.
# Checks, for n <= NMAX: b-files of A166406/A166100/A166407/A166101 reproduce;
# S/N has denominator 3 exactly when n is in A166101 and is an integer otherwise;
# the denominator-3 cases are exactly N = 3 m^2 with every prime factor p != 3 of m
# congruent to 2 mod 3 (then S/N = -2^w/3, w = number of such primes).
import sys
from fractions import Fraction

def jacobi(a, n):
  a %= n; r = 1
  while a:
    while a % 2 == 0:
      a //= 2
      if n % 8 in (3, 5): r = -r
    a, n = n, a
    if a % 4 == 3 and n % 4 == 3: r = -r
    a %= n
  return r if n == 1 else 0

def rd(f):
  return {int(l.split()[0]): int(l.split()[1]) for l in open(f) if l.strip() and not l.startswith("#")}
b406, b100, b407, b101 = rd("b166406.txt"), rd("b166100.txt"), rd("b166407.txt"), rd("b166101.txt")
A101 = set(b101.values())
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
def factor(m):
  f = {}; p = 2
  while p * p <= m:
    while m % p == 0: f[p] = f.get(p, 0) + 1; m //= p
    p += 1
  if m > 1: f[m] = f.get(m, 0) + 1
  return f
bad = 0; den3 = []
for n in range(0, NMAX + 1):
  N = 2 * n + 1
  S = 0; plus = 0
  for i in range(1, N + 1):
    j = jacobi(i, N); S += i * j
    if j == 1: plus += i
  if n in b406 and b406[n] != -S: bad += 1; print("A166406", n)
  if n in b100 and b100[n] != plus: bad += 1; print("A166100", n)
  B = Fraction(S, N)
  if n in b407 and b407[n] != (3 * Fraction(-S, N)).__floor__(): bad += 1; print("A166407", n)
  nonint100 = (plus % N != 0)
  if B.denominator not in (1, 3): bad += 1; print("other denominator", n, B)
  if (B.denominator == 3) != nonint100: bad += 1; print("conjecture fails", n)
  if n <= max(A101) and (n in A101) != nonint100: bad += 1; print("A166101 b-file", n)
  # predicted denominator-3 set
  pred = False
  if N % 3 == 0 and N % 9 != 0 or True:
    if N % 3 == 0:
      m2 = N // 3
      r = int(round(m2 ** 0.5))
      if r * r == m2:
        ps = [p for p in factor(r) if p != 3]
        if all(p % 3 == 2 for p in ps):
          pred = True
          if B != Fraction(-(2 ** len(ps)), 3): bad += 1; print("value", n, B)
  if pred != (B.denominator == 3): bad += 1; print("characterisation fails", n)
  if B.denominator == 3: den3.append(n)
print("n <= %d: denominator-3 cases %d, first %s; problems %d" % (NMAX, len(den3), den3[:12], bad))
sys.exit(1 if bad else 0)
