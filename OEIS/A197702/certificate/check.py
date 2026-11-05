# A197702 check: brute-force a(n) from signed sums of odd numbers, the
# characterization of S_k = {+-1 +-3 ... +-(2k-1)} used in Lean, and the
# conjectured rule (as `rule` in A197702_mathlib.lean) against the b-file.
#
# Usage: python3 check.py [b197702.txt]
# (b-file from https://oeis.org/A197702/b197702.txt, n = 1..10000)
#
import sys, math

N    = 20000
KMAX = 200

# S is the set of signed sums with k terms, built term by term.
# good() is the Lean characterization: |m| <= k^2, m = k^2 mod 2,
# m != +-(k^2 - 4).
#
def good(k, m):
  K = k * k
  return ( (-K <= m) and (m <= K) and (((K - m) % 2) == 0) and
           (m != K - 4) and (m != 4 - K) )

best = {}
S    = {0}
ok   = True
for k in range(0, KMAX):
  if k > 0:
    S = {s + 2 * k - 1 for s in S} | {s - 2 * k + 1 for s in S}
  K = k * k
  if k <= 60:
    ok = ok and (S == {m for m in range(-K, K + 1) if good(k, m)})
  for m in S:
    if (0 < m) and (m <= N) and (k > 0) and (m not in best):
      best[m] = k
print("S_k characterization holds for k <= 60:", ok)

def rule(n):
  k = math.isqrt(n - 1) + 1
  d = k * k - n
  if d == 0:
    return k
  if d == 4:
    return k + 2
  return ( k + 1 if (d % 2) == 1 else k )

print("rule = brute force for 1 <= n <=", N, ":", all(best[n] == rule(n) for n in range(1, N + 1)))

if len(sys.argv) > 1:
  bf = {}
  for line in open(sys.argv[1]):
    p = line.split()
    if (len(p) == 2) and (not line.startswith("#")):
      bf[int(p[0])] = int(p[1])
  print("b-file terms:", len(bf), " rule matches b-file:", all(rule(n) == v for n, v in bf.items()))
