#!/usr/bin/env python3
# Search for y with sigma(y) = n! for n in [N0, N1].
#
# A witness is a list of distinct primes q with exponents a such that
# prod sigma(q^a) = n!.  We fill the odd-prime part of n! by depth-first
# search from the largest prime down, then finish the power of 2 with
# Mersenne primes 2^k-1 (sigma = 2^k), whose exponents k have a subset sum
# equal to the leftover 2-adic exponent.
#
# Output: one line per n, "n q^a q^a ...".
#
import sys, random, math
import numpy as np

N0, N1 = int(sys.argv[1]), int(sys.argv[2])
B      = int(sys.argv[3]) if len(sys.argv) > 3 else 10**7
seed   = int(sys.argv[4]) if len(sys.argv) > 4 else 1
random.seed(seed)

# Smallest-prime-factor sieve up to B+2.
#
spf = np.zeros(B+3, dtype=np.int32)
for i in range(2, int(math.isqrt(B+2))+1):
  if spf[i] == 0:
    blk = spf[i*i::i]
    blk[blk == 0] = i
spf_l = spf.tolist()

def is_prime_small(q):
  return (q >= 2) and (spf_l[q] == 0)

def factor_small(m):
  f = {}
  while m > 1:
    p = spf_l[m]
    if p == 0:
      p = m
    f[p] = f.get(p, 0) + 1
    m //= p
  return f

def factor_trial(m, plist):
  f = {}
  for p in plist:
    if (m % p) == 0:
      e = 0
      while (m % p) == 0:
        m //= p
        e += 1
      f[p] = e
  return f, m

def isprime_mr(n):
  if n < 2:
    return False
  for p in (2,3,5,7,11,13,17,19,23,29,31,37):
    if (n % p) == 0:
      return n == p
  d, s = n-1, 0
  while (d % 2) == 0:
    d //= 2
    s += 1
  for a in (2,3,5,7,11,13,17,19,23,29,31,37):
    x = pow(a, d, n)
    if (x == 1) or (x == n-1):
      continue
    for _ in range(s-1):
      x = x*x % n
      if x == n-1:
        break
    else:
      return False
  return True

MERS = [2,3,5,7,13,17,19]

PRE = []
for q in range(3, B+1, 2):
  if spf_l[q] != 0:
    continue
  f = factor_small(q+1)
  if max(f) <= N1:
    PRE.append((q, f))

def build_atoms(n):
  plist = [p for p in range(2, n+1) if is_prime_small(p)]
  E = {p: 0 for p in plist}
  for p in plist:
    t = n
    while t:
      t //= p
      E[p] += t
  atoms = []
  # a = 1: sigma(q) = q+1.
  #
  for q, f in PRE:
    if max(f) <= n and all(f[p] <= E[p] for p in f):
      atoms.append((q, 1, f))
  # a >= 2, small q (including q = 2).
  #
  for q in range(2, 20000):
    if not is_prime_small(q):
      continue
    for a in range(2, 40):
      s = (q**(a+1) - 1)//(q - 1)
      f, r = factor_trial(s, plist)
      if r == 1 and all(f[p] <= E[p] for p in f):
        atoms.append((q, a, f))
      if s > 10**60:
        break
  return plist, E, atoms

def solve(n, tries=2000):
  plist, E, atoms = build_atoms(n)
  bigp = {}
  for at in atoms:
    f = at[2]
    odd = [p for p in f if p > 2]
    if odd:
      bigp.setdefault(max(odd), []).append(at)
  oddp = sorted([p for p in plist if p > 2], reverse=True)
  merset = set((1 << k) - 1 for k in MERS)

  for t in range(tries):
    w    = random.choice([-1.0, -0.3, 0.0, 0.3, 1.0])
    rem  = dict(E)
    used = set()
    sol  = []
    ok   = True
    for p in oddp:
      while rem[p] > 0:
        cands = [at for at in bigp.get(p, []) if (at[0] not in used) and (at[0] not in merset) and all(at[2][r] <= rem[r] for r in at[2])]
        if not cands:
          ok = False
          break
        # Prefer atoms that use few 2s (save 2s for later), with randomness.
        #
        cands.sort(key=lambda at: (w*at[2].get(2, 0) + random.random()*3))
        at = cands[0] if (random.random() < 0.7) else random.choice(cands[:5])
        used.add(at[0])
        sol.append((at[0], at[1]))
        for r in at[2]:
          rem[r] -= at[2][r]
      if not ok:
        break
    if not ok:
      continue
    # Finish 2-adic exponent with distinct Mersenne exponents.
    #
    r2 = rem[2]
    avail = [k for k in MERS if ((1 << k) - 1) not in used]
    reach = {0: []}
    for k in avail:
      new = {}
      for s, L in reach.items():
        if (s + k) <= r2 and (s + k) not in reach:
          new[s+k] = L + [k]
      reach.update(new)
    if r2 in reach:
      for k in reach[r2]:
        sol.append(((1 << k) - 1, 1))
      return sol
  return None

for n in range(N0, N1+1):
  s = solve(n)
  if s is None:
    print(n, "FAIL", flush=True)
    continue
  # Verify.
  #
  qs = [q for q, a in s]
  assert len(set(qs)) == len(qs)
  prod = 1
  for q, a in s:
    assert isprime_mr(q)
    prod *= (q**(a+1) - 1)//(q - 1)
  assert prod == math.factorial(n)
  print(n, " ".join(f"{q}^{a}" for q, a in sorted(s)), flush=True)
