"""A078128 / A078130: partitions into cubes > 1.

Computes a(n) (A078128) by the coin-change recurrence over all cubes k^3,
k >= 2, up to N, then checks:
* the coin-change count with only 8 and 27 is >= m + 1 when n >= 216 m + 182
  (the bound proved in Lean as `a_lower`);
* b(k) = largest n with a(n) <= k for k = 0..5 (b(0) = 154, b(1) = 218);
* the 63 terms of A078130 (a(n) = 1, n >= 1);
* agreement with the b-file b078128.txt if given as argv[1].
Usage: python3 check.py [b078128.txt]
"""
import sys

N = 20000
cubes = [k ** 3 for k in range(2, 40) if k ** 3 <= N]
a = [0] * (N + 1)
a[0] = 1
for c in cubes:
  for n in range(c, N + 1):
    a[n] += a[n - c]

w = [0] * (N + 1)
w[0] = 1
for c in (8, 27):
  for n in range(c, N + 1):
    w[n] += w[n - c]
for n in range(N + 1):
  if n >= 182:
    m = (n - 182) // 216
    assert w[n] >= m + 1, n
  assert w[n] <= a[n]

for k in range(6):
  print("b(%d) = %d" % (k, max(n for n in range(1, N + 1) if a[n] <= k)))
S = [n for n in range(1, N + 1) if a[n] == 1]
print(len(S), "terms with a(n) = 1, last", S[-1])
assert S[-1] == 218 and len(S) == 63

if len(sys.argv) > 1:
  cnt = 0
  for line in open(sys.argv[1]):
    if line.strip() and not line.startswith("#"):
      n, v = map(int, line.split())
      assert a[n] == v, n
      cnt += 1
  print("b-file agrees on", cnt, "terms")
print("OK")
