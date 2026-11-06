# A053029 / A053031: zeros of Fibonacci numbers in one Pisano period mod m,
# for m <= N; check both characterizations (prime-factor reading) and the
# OEIS data terms.
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
def zeros(m):
  if m == 1: return 1
  a, b, k, z = 0, 1, 0, 0
  while True:
    a, b, k = b, (a + b) % m, k + 1
    if a == 0: z += 1
    if a == 0 and b == 1: return z
def pf(n):
  s, d = set(), 2
  while d * d <= n:
    while n % d == 0: s.add(d); n //= d
    d += 1
  if n > 1: s.add(n)
  return s
Z = {m: zeros(m) for m in range(1, N + 1)}
def rhs(m, val, mults):
  for e in mults:
    if m % e == 0:
      k = m // e
      if k % 2 == 1 and all(Z[p] == val for p in pf(k)): return True
  return False
bad29 = [m for m in range(3, N + 1) if (Z[m] == 4) != rhs(m, 4, (1, 2))]
bad31 = [m for m in range(1, N + 1) if (Z[m] == 1) != rhs(m, 1, (1, 2, 4))]
D29 = [5,10,13,17,25,26,34,37,50,53,61,65,73,74,85,89,97,106,109,113,122,125,130,137,146,149,157,169,170,173,178,185,193,194,197,218,221,226,233,250,257,265,269,274,277,289,293,298,305,313,314,317,325,337,338,346]
D31 = [1,2,4,11,19,22,29,31,38,44,58,59,62,71,76,79,101,116,118,121,124,131,139,142,151,158,179,181,191,199,202,209,211,229,236,239,242,251,262,271,278,284,302,311,316,319,331,341,349,358,359,361,362,379,382,398]
assert [m for m in range(1, D29[-1] + 1) if Z[m] == 4] == D29
assert [m for m in range(1, D31[-1] + 1) if Z[m] == 1] == D31
print("data terms agree; A053029 mismatches (3..%d):" % N, bad29, "; A053031 mismatches (1..%d):" % N, bad31)
print("m = 1, 2 zeros:", Z[1], Z[2])
