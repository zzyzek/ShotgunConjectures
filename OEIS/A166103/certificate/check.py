# Uses the A166100 b-file (S(2n+1) for n <= 131071; path in argv[1], not stored here,
# https://oeis.org/A166100/b166100.txt) and the A166102 b-file.
# Checks for odd k <= 262143:
#  (1) k does not divide S(k)  <=>  k = 3 m^2 with all prime factors of m equal to 3 or = 5 mod 6 (m in A166104);
#  (2) S(k) for small k recomputed from Jacobi symbols agrees with the b-file;
#  (3) in the case k = 3^e N (e odd, N = n^2, 3 not dividing n):
#      S(k)/k = (3^e phi(N) - prod_{p | N} (1 - (p/3))) / 6;
#  (4) A166102 b-file = 3 * (A166104)^2 in order.
import sys
from sympy import factorint, jacobi_symbol, totient
S = {}
for line in open(sys.argv[1]):
  t = line.split()
  if len(t) == 2 and not line.startswith('#'): S[2 * int(t[0]) + 1] = int(t[1])
K = max(S)
def good_m(m):
  return all(p == 3 or p % 6 == 5 for p in factorint(m))
exc = set()
m = 1
while 3 * m * m <= K:
  if good_m(m): exc.add(3 * m * m)
  m += 1
for k in range(1, 400, 2):
  assert S[k] == sum(i for i in range(1, k + 1) if jacobi_symbol(i, k) == 1)
bad = [k for k in sorted(S) if S[k] % k != 0]
assert set(bad) == exc, (sorted(set(bad) ^ exc)[:10])
for k in sorted(S):
  f = factorint(k)
  e = f.get(3, 0)
  if e % 2 == 1 and all(v % 2 == 0 for p, v in f.items() if p != 3):
    N = k // 3 ** e
    P = 1
    for p in factorint(N): P *= (1 - (1 if p % 3 == 1 else -1))
    assert 6 * S[k] == k * (3 ** e * totient(N) - P), k
b102 = [int(l.split()[1]) for l in open('b166102.txt') if l.strip() and not l.startswith('#')]
assert [x for x in b102 if x <= K] == sorted(exc)
gen = sorted(3 * m * m for m in range(1, 1000) if good_m(m))
assert b102 == gen[:len(b102)]
print("odd k <= %d: %d exceptions, all = 3 m^2 with m in A166104; formula (3) holds; A166102 b-file (%d terms) matches" % (K, len(bad), len(b102)))
