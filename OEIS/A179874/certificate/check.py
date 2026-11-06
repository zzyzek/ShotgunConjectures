# B(h) = sum k^2 / sum k over 1 <= k <= h, gcd(k,h) = 1 (A179873 via A179871).
# Checks for h <= H: B(h) integer <=> h squarefree and 3 | 2h + (-1)^omega(h); then B = (2h + (-1)^omega)/3,
# odd; values nondecreasing in h; agreement with the A179873 b-file; A179874 data vs distinct values.
from fractions import Fraction
from math import gcd
from sympy import factorint
import sys
H = int(sys.argv[1])
vals = []
for h in range(1, H + 1):
  ks = [k for k in range(1, h + 1) if gcd(k, h) == 1]
  B = Fraction(sum(k * k for k in ks), sum(ks))
  f = factorint(h)
  sqf = all(e == 1 for e in f.values())
  s = (-1) ** len(f)
  pred = sqf and (2 * h + s) % 3 == 0
  assert (B.denominator == 1) == pred, h
  if pred:
    assert B == (2 * h + s) // 3 and B % 2 == 1
    vals.append(int(B))
assert all(vals[i] <= vals[i + 1] for i in range(len(vals) - 1))
b = [int(l.split()[1]) for l in open('b179873.txt') if l.strip() and not l.startswith('#')]
n = min(len(b), len(vals)); assert b[:n] == vals[:n]
data174 = [1,3,7,11,15,19,23,27,31,35,37,39,47,55,57,59,61,63,67,71,73,75,77,79,87,89,91,95,97,99,111,113,115,119,121,125,127,131,135,137,143,145,151,151,153,155,157,159,165,167]
distinct = sorted(set(vals))
print("h <= %d: %d integral values, all odd, nondecreasing; b-file agrees on %d terms" % (H, len(vals), n))
print("A179874 data == distinct values?", data174 == distinct[:len(data174)])
print("distinct values from 145 on:", [v for v in distinct if 140 <= v <= 170])
d2 = data174[:42] + data174[43:]
print("A179874 data with the second 151 removed == distinct values?", d2 == distinct[:len(d2)])
