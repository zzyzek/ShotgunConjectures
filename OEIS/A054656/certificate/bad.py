# For each prime p <= P and m <= M: is m a sum of distinct primes avoiding p?
# Print the (m, p) failures.
import sys
P, M = int(sys.argv[1]), int(sys.argv[2])
def primes(n):
  s = [True]*(n+1); s[0]=s[1]=False
  for i in range(2, int(n**.5)+1):
    if s[i]:
      for j in range(i*i, n+1, i): s[j]=False
  return [i for i in range(n+1) if s[i]]
pr = primes(max(P, M))
bad = []
for p in [q for q in pr if q <= P]:
  reach = 1
  for q in pr:
    if q != p and q <= M: reach |= reach << q
  reach &= (1 << (M+1)) - 1
  for m in range(M+1):
    if not (reach >> m) & 1: bad.append((m, p))
from collections import defaultdict
d = defaultdict(list)
for m, p in bad: d[m].append(p)
for m in sorted(d):
  ps = d[m]
  print(m, ps if len(ps) < 20 else ("all %d primes" % len(ps)))
