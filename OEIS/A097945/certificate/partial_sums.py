# Partial sums S(N) = sum_{n<=N} mu(n)/phi(n), by a linear sieve.
# Pairing n <-> 2n for odd n gives S(N) = sum over odd m in (N/2, N] of mu(m)/phi(m).
#
import sys
N = int(sys.argv[1])
mu  = [1] * (N + 1)
phi = list(range(N + 1))
isc = bytearray(N + 1)
primes = []
for i in range(2, N + 1):
  if not isc[i]:
    primes.append(i); mu[i] = -1; phi[i] = i - 1
  for p in primes:
    if i * p > N: break
    isc[i * p] = 1
    if i % p == 0:
      mu[i * p] = 0; phi[i * p] = phi[i] * p; break
    mu[i * p] = -mu[i]; phi[i * p] = phi[i] * (p - 1)
s = 0.0
mark = 10
for n in range(1, N + 1):
  s += mu[n] / phi[n]
  if n == mark:
    print(n, s); mark *= 10
