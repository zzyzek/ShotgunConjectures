# Check of the A227345 boundary conjecture.
#  1. Recompute T(n,k) (distinct-part partitions of n with boundary size k)
#     by brute force for n <= 30 and compare with the b-file rows.
#  2. From the b-file (rows n = 1..100), check T(n,k) > 0 iff 3k^2 <= 4n.
#  3. Check the explicit witnesses of the proof for n <= 400.
# Usage: python3 check.py b227345.txt
#
import sys

def bdry(S):
  return sum(1 for p in S if not (((p - 1) in S) and ((p + 1) in S)))

def parts(n, mx):
  if n == 0:
    yield frozenset()
    return
  for p in range(min(n, mx), 0, -1):
    for r in parts(n - p, p - 1):
      yield r | {p}

def witness(n, k):
  # Pairs {3j+1, 3j+2} for j < m-1 (or j < m), then a top pair / singleton.
  #
  m = k // 2
  if (k % 2) == 0:
    A = {x for j in range(m - 1) for x in (3*j + 1, 3*j + 2)}
    b = n - sum(A) - (3*m - 2)
    return A | {3*m - 2, b}
  A = {x for j in range(m) for x in (3*j + 1, 3*j + 2)}
  return A | {n - sum(A)}

vals = [int(l.split()[1]) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
rows, i = {}, 0
for n in range(1, 101):
  rows[n] = vals[i:i + n]; i += n

for n in range(1, 31):
  cnt = [0] * (n + 1)
  for S in parts(n, n):
    cnt[bdry(S)] += 1
  assert cnt[0] == 0 and cnt[1:] == rows[n], n
print("brute force = b-file rows, n <= 30: ok")

for n in range(1, 101):
  for k in range(1, n + 1):
    assert (rows[n][k - 1] > 0) == (3*k*k <= 4*n), (n, k)
print("T(n,k) > 0 iff 3k^2 <= 4n on b-file rows n <= 100: ok")

for n in range(1, 401):
  for k in range(1, n + 1):
    if 3*k*k <= 4*n:
      W = witness(n, k)
      assert (sum(W) == n) and (min(W) >= 1) and (bdry(W) == k) and (len(W) == k if k % 2 else True), (n, k, W)
print("witnesses valid for n <= 400: ok")
