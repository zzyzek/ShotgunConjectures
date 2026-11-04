# A008578 (Gerasimova 2013): {1} u primes = {k : sigma(k) > k * Omega(k)}.
# Checks k < 2*10^6 with a sieve; also lists composites with equality.
#
N = 2 * 10**6
sig = [0] * N
for d in range(1, N):
  for m in range(d, N, d): sig[m] += d
Om = [0] * N
rem = list(range(N))
for p in range(2, N):
  if rem[p] == p and Om[p] == 0:
    for m in range(p, N, p):
      while rem[m] % p == 0: rem[m] //= p; Om[m] += 1
isp = [False, False] + [Om[k] == 1 for k in range(2, N)]
bad = [k for k in range(1, N) if (sig[k] > k * Om[k]) != (k == 1 or isp[k])]
eq = [k for k in range(2, N) if not isp[k] and sig[k] == k * Om[k]]
print("mismatches:", bad[:10], "composites with equality:", eq)
