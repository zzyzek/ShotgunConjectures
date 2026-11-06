# T(n,k) from the entry's recurrence equals
#   2^(nk) * (2n + 2k - n*2^(1-k) - k*2^(1-n)) - 2 * S(n,k),
# S(n,k) = sum of ranks over GF(2) of all n x k 0-1 matrices; hence T(n,k) = T(k,n).
# Checks: recurrence vs data/b-file; closed form vs recurrence (n,k <= 40, S from the
# row recurrence); S from the row recurrence vs brute-force rank sums (n*k <= 16);
# symmetry of T for n,k <= 40.
import sys
from fractions import Fraction as F
from functools import lru_cache
from itertools import product

@lru_cache(None)
def T(n, k):
  if n == 0 or k == 0: return 0
  t3 = (n - 1) * (2**k - 1) * 2**((n - 2) * k + 1) if n >= 2 else 0
  return ((2**(k + 1) - 2) * 2**((n - 1) * k) + 2**((n - 1) * (k - 1)) * ((k - 2) * 2**k + 2)
          + t3 + T(n - 1, k) + 2**(n - 1) * (2**k - 1) * T(n - 1, k - 1))

@lru_cache(None)
def S(n, k):
  # condition on the first row: zero (rank of the rest) or v != 0 (1 + rank of the rest mod v)
  if n == 0 or k == 0: return 0
  return S(n - 1, k) + (2**k - 1) * (2**((n - 1) * k) + 2**(n - 1) * S(n - 1, k - 1))

def rank2(rows, k):
  rows = list(rows); r = 0
  for c in range(k):
    piv = next((i for i in range(r, len(rows)) if (rows[i] >> c) & 1), None)
    if piv is None: continue
    rows[r], rows[piv] = rows[piv], rows[r]
    for i in range(len(rows)):
      if i != r and (rows[i] >> c) & 1: rows[i] ^= rows[r]
    r += 1
  return r

bad = 0
bf = [int(l.split()[1]) for l in open("b058347.txt") if l.strip() and not l.startswith("#")]
anti = [T(c - n, n) for c in range(200) for n in range(c + 1)]
if anti[:len(bf)] != bf: bad += 1; print("b-file mismatch")
for n in range(0, 5):
  for k in range(0, 5):
    if n * k <= 16:
      brute = sum(rank2(rows, k) for rows in product(range(2**k), repeat=n))
      if brute != S(n, k): bad += 1; print("rank sum", n, k)
for n in range(0, 41):
  for k in range(0, 41):
    closed = F(2**(n * k)) * (2*n + 2*k - n * F(2, 2**k) - k * F(2, 2**n)) - 2 * S(n, k)
    if closed != T(n, k): bad += 1; print("closed form", n, k)
    if T(n, k) != T(k, n): bad += 1; print("asymmetric", n, k)
print("b-file terms", len(bf), "problems", bad)
sys.exit(1 if bad else 0)
