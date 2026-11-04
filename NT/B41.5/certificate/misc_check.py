import sys; sys.path.insert(0, '.')
from math import gcd, comb, isqrt
from mr import is_prime
# NT-B2.3: n = 2^2 7^2 p^2 with sigma(n) - 2n an odd square.
# sigma(n) - 2n = 7*57*(p^2+p+1) - 392 p^2 = 7 (p^2 + 57 p + 57).
#
print("B2.3:")
for p in range(3, 10**6):
  if p == 7 or not is_prime(p): continue
  v = 7*(p*p + 57*p + 57)
  r = isqrt(v)
  if r*r == v: print("  p =", p, "abundance =", v, "=", r, "^2")
# smallest n with odd-square abundance (brute force, n <= 2e6)
N = 2*10**6
s = [0]*(N+1)
for a in range(1, N+1):
  for q in range(a, N+1, a): s[q] += a
first = None
for n in range(1, N+1):
  ab = s[n] - 2*n
  if ab > 0 and ab % 2 == 1 and isqrt(ab)**2 == ab: first = n; break
print("  least n <= 2e6 with odd square abundance:", first, s[first]-2*first if first else None)
# NT-B31.5: n = 28, r = 5, s = 14
g = gcd(comb(28, 5), comb(28, 14))
print("B31.5: gcd =", g)
# all counterexamples with n <= 60
ce = []
for n in range(2, 61):
  for r in range(1, n//2+1):
    for s_ in range(r+1, n//2+1):
      g = gcd(comb(n, r), comb(n, s_))
      P, m, q = 1, g, 2
      while q*q <= m:
        while m % q == 0: P = max(P, q); m //= q
        q += 1
      if m > 1: P = max(P, m)
      if P <= r: ce.append((n, r, s_, g))
print("  counterexamples n<=60:", ce)
# NT-B41.5: f(n) = phi(n)+1; find all n <= 2000 reaching 5 or 7
def phi(n):
  r, m, p = n, n, 2
  while p*p <= m:
    if m % p == 0:
      while m % p == 0: m //= p
      r -= r//p
    p += 1
  if m > 1: r -= r//m
  return r
def end(n):
  while n > 2 and phi(n) + 1 != n: n = phi(n) + 1
  return n
print("B41.5: ->5", [n for n in range(1, 2001) if end(n) == 5], "->7", [n for n in range(1, 2001) if end(n) == 7])
# NT-F23.2: n! = 2^a + 2^b and n! = 2^a - 2^b (a > b), n <= 40
f = 1
for n in range(1, 41):
  f *= n
  plus  = [(a, b) for a in range(0, f.bit_length()+1) for b in range(0, a+1) if 2**a + 2**b == f]
  minus = [(a, b) for a in range(0, f.bit_length()+2) for b in range(0, a) if 2**a - 2**b == f]
  if plus or minus: print("F23.2: n =", n, "plus", plus, "minus", minus)
