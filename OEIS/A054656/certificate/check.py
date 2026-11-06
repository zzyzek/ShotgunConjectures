# A054656: compute a(n) from the definition (primes p <= n with n - p not a
# sum of distinct primes avoiding p) for n <= N, compare with the OEIS data
# terms and with the conjectured formula for n >= 23.
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
DATA = [0,0,0,1,2,0,3,1,2,2,0,4,1,3,1,1,1,2,1,2,1,1,1,2,1,1,0,1,0,1,1,0,1,1,
        0,2,0,1,1,0,0,1,1,1,1,1,0,2,1,1,0,1,0,1,1,0,0,1,0,1,1,0,1,1,0,2,0,1,
        1,0,0,1,1,1,1,1,0,2,0,1,1,0,0,1,1,1,0]
sieve = [True]*(N+1); sieve[0] = sieve[1] = False
for i in range(2, int(N**.5)+1):
  if sieve[i]:
    for j in range(i*i, N+1, i): sieve[j] = False
pr = [i for i in range(N+1) if sieve[i]]
full = 1
for q in pr: full |= full << q
mask = (1 << (N+1)) - 1
full &= mask
reach = {}
for p in pr:
  r = 1
  for q in pr:
    if q != p: r |= r << q
  reach[p] = r & mask
def a(n):
  return sum(1 for p in pr if p <= n and not (reach[p] >> (n-p)) & 1)
def conj(n):
  P = lambda k: k >= 0 and sieve[k]
  if P(n-6) and P(n-4): return 2
  if P(n-6) or P(n-4) or P(n-1): return 1
  return 0
vals = [a(n) for n in range(N+1)]
assert vals[:len(DATA)] == DATA, "data mismatch"
bad = [n for n in range(23, N+1) if vals[n] != conj(n)]
print("data terms a(0..%d) agree" % (len(DATA)-1))
print("formula mismatches for 23 <= n <= %d:" % N, bad)
print("formula fails at n = 22:", vals[22], conj(22))
