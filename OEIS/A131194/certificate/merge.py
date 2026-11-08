# A131194 (share >= 3 digits) / A133835 (share >= 2): orbit of a seed under
# next(p) = least prime q > p whose digit multiset shares >= s digits with p.
# Check every prime seed below LIM merges with the main orbit (seed 101 / 11).
import sys
from collections import Counter
from sympy import nextprime, isprime
s = int(sys.argv[1]); main_seed = int(sys.argv[2]); LIM = int(sys.argv[3]); CAP = int(sys.argv[4])
def share(a, b):
  ca, cb = Counter(str(a)), Counter(str(b)); return sum((ca & cb).values())
memo = {}
def nxt(p):
  if p in memo: return memo[p]
  q = nextprime(p)
  while share(p, q) < s: q = nextprime(q)
  memo[p] = q; return q
main = set(); p = main_seed
while p < CAP: main.add(p); p = nxt(p)
worst = 0; fails = []
for seed in range(10**(s-1), LIM):
  if not isprime(seed): continue
  p = seed
  while p not in main and p < CAP: p = nxt(p)
  if p in main: worst = max(worst, p)
  else: fails.append(seed)
print("share", s, "seeds below", LIM, "unmerged below cap", CAP, ":", fails[:10], "latest merge point", worst)
