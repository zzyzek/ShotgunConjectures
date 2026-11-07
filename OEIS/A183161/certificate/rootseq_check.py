# Recompute rootSeq c n = [t^n] (1-t)^(-c) R (1-3t) (1-t)^(-2n-1), R = 1/((1-t) C),
# C = sqrt(1-4u) = 1 - 2 sum Cat(k) u^(k+1), u = t^2/(1-t)^2, with exact integers,
# and compare with the cached OEIS b-terms of A183161 / A219197 (and A218622 = A183161 mod 4).
#
import sys, re
from math import comb
N = 60
def mul(a, b):
  r = [0]*N
  for i, x in enumerate(a):
    if x:
      for j in range(N - i): r[i+j] += x*b[j]
  return r
J = [1]*N
u = mul([0, 0, 1] + [0]*(N-3), mul(J, J))
cat = lambda k: comb(2*k, k)//(k+1)
C = [1] + [0]*(N-1); up = u[:]
for k in range(N):
  C = [c - 2*cat(k)*x for c, x in zip(C, up)]
  up = mul(up, u)
T = mul([1, -1] + [0]*(N-2), C)
R = [0]*N; R[0] = 1
for n in range(1, N): R[n] = -sum(T[k]*R[n-k] for k in range(1, n+1))
RS = mul(R, [1, -3] + [0]*(N-2))
def root(c, n): return sum(RS[j]*comb(2*n+c+(n-j), n-j) for j in range(n+1))
def cache(a):
  s = open(sys.argv[1] + '/' + a + '.txt').read()
  return [int(x) for x in ''.join(re.findall(r'^%[STU] ' + a + r' (\S+)', s, re.M)).split(',') if x]
for a, f in [('A183161', lambda n: root(0, n)), ('A219197', lambda n: root(1, n)),
             ('A218622', lambda n: root(0, n) % 4)]:
  d = cache(a); m = min(len(d), N)
  ok = all(f(n) == d[n] for n in range(m))
  print(a, 'terms', m, 'match' if ok else 'MISMATCH')
