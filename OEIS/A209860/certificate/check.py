# Checks for the A209860 / A209861 / A209862 conjecture (A054429 commutes with A209861).
# Usage: python3 check.py b209860.txt b209861.txt b209862.txt
#  1. g = A209642 (the entry's Scheme loop); A209861(n) = #{i : g(i) < g(n)} (rank of
#     A209642(n) in its ascending listing A209641); A209862 = inverse.  Compare with b-files.
#  2. The set of values of g below 4^15 equals the A209641 membership test (entry's Scheme).
#  3. Closed form g(n) + 2^E = 2^E * 2^pop + tau(n), E = 2*len - pop, 2*tau < 2^E.
#  4. The conjecture itself for n < 2^15.
#
import sys

def g(n):
  s, i = 0, 1
  while n:
    if n % 2 == 0:
      n //= 2; s = 4*s + 1
    else:
      n = (n - 1) // 2; s = (s + i) * 2
    i *= 4
  return s

def member_A209641(n):
  lev = 0
  while True:
    if n == 0: return lev == 0
    if lev < 0: return False
    if n % 2 == 0:
      n //= 2; lev += 1
    else:
      m = (n - 1) // 2
      if (m % 2 == 1) and (((m - 1) // 2) % 2 == 0) and ((m - 1) // 2 != 0): return False
      n = m; lev -= 1

def ln(n): return n.bit_length()
def pop(n): return bin(n).count('1')
def E(n): return 2*ln(n) - pop(n)
def tau(n):
  if n == 0: return 0
  q = n // 2
  return tau(q) if (n % 2 == 1) else (2**E(q) + tau(q))
def c(n): return 3 * 2**(ln(n) - 1) - 1 - n

def bfile(f): return [int(l.split()[1]) for l in open(f) if l.strip() and not l.startswith('#')]

N = 15
gs = [g(n) for n in range(2**N)]
order = sorted(range(2**N), key=lambda n: gs[n])
a862 = order
a861 = [0] * (2**N)
for m, n in enumerate(order): a861[n] = m
fix = [n for n in range(2**N) if a861[n] == n]
b860, b861, b862 = bfile(sys.argv[1]), bfile(sys.argv[2]), bfile(sys.argv[3])
assert a862 == b862[:2**N] and a861 == b861[:2**N]
assert fix == [x for x in b860 if x < 2**N]
print("A209861, A209862 (n < 2^15) and A209860 b-file reproduced: ok")

vals = set(gs)
mem = [x for x in range(4**8) if member_A209641(x)]
assert mem == sorted(v for v in vals if v < 4**8)
print("A209641 membership test = values of g below 4^8: ok")

for n in range(1, 2**N):
  assert gs[n] + 2**E(n) == 2**E(n) * 2**pop(n) + tau(n) and 2*tau(n) < 2**E(n)
print("closed form and tau bound, n < 2^15: ok")

for n in range(1, 2**N):
  assert a861[c(n)] == c(a861[n]) and a862[c(n)] == c(a862[n])
print("conjecture holds for 1 <= n < 2^15: ok")
