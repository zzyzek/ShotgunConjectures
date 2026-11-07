# Decode a CaDiCaL model for gen.py's encoding (K values per n >= 2) and verify from scratch,
# using only the values at primes, that f has no three consecutive zeros among 1..N.
# Writes the prime values as "p v" lines.
import sys
N = int(sys.argv[1]); K = int(sys.argv[2]); model = sys.argv[3]; out = sys.argv[4]
pos = set()
for line in open(model):
  if line.startswith('v'):
    for t in line.split()[1:]:
      x = int(t)
      if x > 0: pos.add(x)
val = [None]*(N+1)
for x in pos:
  n = (x-1)//K + 2; v = (x-1) % K
  if n <= N:
    assert val[n] is None; val[n] = v
spf = list(range(N+1))
for i in range(2, int(N**0.5)+1):
  if spf[i] == i:
    for j in range(i*i, N+1, i):
      if spf[j] == j: spf[j] = i
g = [0]*(N+1)
with open(out, 'w') as o:
  for n in range(2, N+1):
    if spf[n] == n:
      g[n] = val[n]; o.write('%d %d\n' % (n, val[n]))
    else:
      g[n] = (g[spf[n]] + g[n//spf[n]]) % K
bad = [r for r in range(1, N-1) if g[r] == 0 and g[r+1] == 0 and g[r+2] == 0]
print('N', N, 'K', K, 'zero triples', len(bad), 'zeros', sum(1 for n in range(1, N+1) if g[n] == 0))
