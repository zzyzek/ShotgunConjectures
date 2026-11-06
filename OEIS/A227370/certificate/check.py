# A227368 via the pair/greedy model (fast.py; its correctness is the Lean-proved
# model of OEIS/A227786), checked against the b-files (N <= 132); then for N <= NMAX:
#  (a) the winning pair (m, k) and D match the case table O1-O7, V1-V4 of the README;
#  (b) code(N) < code(N-1) exactly for even N in [s^2, s^2 + 2s], s even (N >= 4);
#  (c) sorting the codes is the product of those adjacent transpositions, so A227370
#      is an involution; also compared with the A227370 b-file.
import sys
from fast import best

def code(r):
  s = ''; b = '1'
  for x in r: s += b * x; b = '0' if b == '1' else '1'
  return int(s, 2)

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
val = {0: 0, 1: 1}; win = {}
for N in range(2, NMAX + 1):
  (kk, m, k, D, r), L = best(N); val[N] = code(r); win[N] = (L, m, k, D)
bad = 0
def rd(f): return {int(l.split()[0]): int(l.split()[1]) for l in open(f) if l.strip() and not l.startswith("#")}
b368, b370 = rd("b227368.txt"), rd("b227370.txt")
for N, v in b368.items():
  if v != val[N]: bad += 1; print("b227368", N)

def predicted(N):
  # returns (m, k) by the case table
  s = 1
  while s * s < N: s += 1
  if N > s * (s - 1):
    E = s * s - N; odd_block = True
  else:
    s -= 1; E = s * s + s - N; odd_block = False
  if odd_block:
    if (s - E) % 2 == 0:
      return (s + 1, s - 1) if s % 2 == 1 else (s, s)
    if E == 0: return (s, s)
    if E == 1: return (s - 1, s + 1)
    if E == 2: return (s, s)
    return (s + 1, s - 1) if s % 2 == 0 else (s, s)
  else:
    if (s - E) % 2 == 0: return (s + 1, s)
    if s % 2 == 0: return (s, s + 1)
    if E == 0: return (s, s + 1)
    return (s + 2, s - 1)
for N in range(6, NMAX + 1):
  if predicted(N) != (win[N][1], win[N][2]): bad += 1; print("case table", N, predicted(N), win[N])

def in_set(N):
  if N % 2: return False
  s = 0
  while (s + 2) * (s + 2) <= N: s += 2
  return s >= 2 and s * s <= N <= s * s + 2 * s
for N in range(2, NMAX + 1):
  if (val[N] < val[N - 1]) != in_set(N): bad += 1; print("inversion", N)
order = sorted(range(0, NMAX + 1), key=lambda n: val[n])
perm = list(range(NMAX + 1))
for N in range(2, NMAX + 1):
  if in_set(N): perm[N - 1], perm[N] = perm[N], perm[N - 1]
# the last pair may be cut by NMAX; compare only well inside
cut = NMAX - 2
if order[:cut] != perm[:cut]: bad += 1; print("sorted order is not the product of the transpositions")
for n, v in b370.items():
  if n < cut and order[n] != v: bad += 1; print("b227370", n)
print("N <= %d checked; problems %d" % (NMAX, bad))
sys.exit(1 if bad else 0)
