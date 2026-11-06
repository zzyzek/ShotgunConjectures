# Compute A165886 from its definition (A091137, A001316) and compare with the b-file
# and with the conjectured A141459(n+1)*A006519(n+1).
from fractions import Fraction
from sympy import primerange
N = 2000
def A091137(n):
  r = 1
  for p in primerange(2, n+2): r *= p**(n//(p-1))
  return r
def A165641(n): return Fraction(A091137(n), 2**bin(n).count('1'))
def A141459(m): return 1 if m == 0 else __import__('math').prod(p for p in primerange(3, m+2) if m % (p-1) == 0)
b = {}
for line in open('b165886.txt'):
  t = line.split()
  if len(t) == 2 and not line.startswith('#'): b[int(t[0])] = int(t[1])
prev = A165641(0); bad = 0
for n in range(N+1):
  cur = A165641(n+1); a = cur/prev; prev = cur
  m = n+1; conj = A141459(m) * (m & -m)
  if a != conj or (n in b and b[n] != a): bad += 1; print("mismatch", n)
print("n = 0 ..", N, "mismatches", bad)
