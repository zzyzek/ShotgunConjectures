# (a) A213648 from its continued-fraction definition for n = 2..400, against the b-file;
# (b) a(n) = z(n) - 1 (z = Fibonacci entry point) for n = 2..10000 against the b-file;
# (c) fixed points a(n) = n for n <= 10000 equal A000057 terms <= 10000;
# (d) z(n) = n + 1 only for primes, n <= 2*10^5.
import sys
from fractions import Fraction

def cf(fr):
  out = []
  p, q = fr.numerator, fr.denominator
  while q:
    a = p // q; out.append(a); p, q = q, p - a * q
  # canonical form: last quotient > 1 (Python's Euclid already gives that unless the cf is [1])
  return out

def val(lst):
  v = Fraction(lst[-1])
  for a in reversed(lst[:-1]): v = a + 1 / v
  return v

def a_def(n):
  m = 1
  while True:
    t = cf(n * val([n] + [1] * m + [n]))
    if t[0] == t[-1]: return m
    m += 1

def z(n):
  a, b, k = 0, 1, 1
  while b % n: a, b, k = b, (a + b) % n, k + 1
  return k

bf = {int(l.split()[0]): int(l.split()[1]) for l in open("b213648.txt") if l.strip() and not l.startswith("#")}
bad = 0
for n in range(2, 401):
  if a_def(n) != bf[n]: bad += 1; print("cf definition mismatch", n)
for n in range(2, 10001):
  if z(n) - 1 != bf[n]: bad += 1; print("z mismatch", n)
fix = [n for n in range(2, 10001) if bf[n] == n]
a57 = [int(l.split()[1]) for l in open("b000057.txt") if l.strip() and not l.startswith("#")]
if fix != [p for p in a57 if p <= 10000]: bad += 1; print("fixed points differ")
def isprime(n):
  if n < 2: return False
  i = 2
  while i * i <= n:
    if n % i == 0: return False
    i += 1
  return True
for n in range(2, 200001):
  if (n % 5) in (2, 3) or n % 2 == 0:
    pass
  if z(n) == n + 1 and not isprime(n): bad += 1; print("composite with z = n+1:", n)
print("fixed points <= 10000:", len(fix), "problems", bad)
sys.exit(1 if bad else 0)
