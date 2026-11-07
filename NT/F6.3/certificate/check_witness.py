# Re-check witness_k5_N400000.txt.gz: lines "p v" give f(p) in Z/5 for all primes p <= N.
# Extends f additively and verifies that no 1 <= r <= N-2 has f(r) = f(r+1) = f(r+2) = 0.
import gzip, sys
path = sys.argv[1] if len(sys.argv) > 1 else 'witness_k5_N400000.txt.gz'
N, K = 400000, 5
fp = {}
for line in gzip.open(path, 'rt'):
  p, v = map(int, line.split()); fp[p] = v
spf = list(range(N+1))
for i in range(2, int(N**0.5)+1):
  if spf[i] == i:
    for j in range(i*i, N+1, i):
      if spf[j] == j: spf[j] = i
primes = [n for n in range(2, N+1) if spf[n] == n]
assert sorted(fp) == primes, 'witness must list exactly the primes <= N'
g = [0]*(N+1)
for n in range(2, N+1):
  g[n] = fp[n] if spf[n] == n else (g[spf[n]] + g[n // spf[n]]) % K
bad = [r for r in range(1, N-1) if g[r] == 0 and g[r+1] == 0 and g[r+2] == 0]
print('primes', len(primes), 'zero triples', len(bad))
