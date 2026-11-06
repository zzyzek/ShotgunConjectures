# Recompute A096127 for n = 2..N from Legendre's formula and compare with
# the b-file; check a(n) = n+1 iff n is a prime power.
import sys

def primes(n):
  s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
  for i in range(2, int(n ** 0.5) + 1):
    if s[i]:
      s[i*i::i] = bytearray(len(s[i*i::i]))
  return [i for i in range(n + 1) if s[i]]

def v(p, m):
  r = 0
  while m:
    m //= p; r += m
  return r

N  = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
ps = primes(N)
pp = set()
for p in ps:
  q = p
  while q <= N:
    pp.add(q); q *= p

b = {}
for line in open("b096127.txt"):
  t = line.split()
  if len(t) == 2 and not line.startswith("#"):
    b[int(t[0])] = int(t[1])

bad = 0
for n in range(2, N + 1):
  a = min(v(p, n*n) // v(p, n) for p in ps if p <= n)
  if (n in b) and (b[n] != a): bad += 1; print("b-file mismatch", n, a, b[n])
  if (a == n + 1) != (n in pp): bad += 1; print("claim fails", n, a)
  if a < n + 1: bad += 1; print("lower bound fails", n)
print("checked n = 2..%d, b-file terms %d, problems %d" % (N, len(b), bad))
sys.exit(1 if bad else 0)
