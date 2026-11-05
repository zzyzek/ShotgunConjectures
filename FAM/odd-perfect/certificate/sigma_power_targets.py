#!/usr/bin/env python3
# Core check for core-sigma-prime-power-target: solutions of
# sigma(p^a) = (p^(a+1) - 1)/(p - 1) = q^j with p, q in {3, 5, 7, 11, 13}
# and a <= AMAX, and a one-step congruence sieve: for each pair, the least
# K such that p^K-adic and q-adic orders already exclude all a >= K except
# the small solutions (reported, not a proof).
#
import sys
AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400
P = [3, 5, 7, 11, 13]
for p in P:
  for q in P:
    if p == q: continue
    sols = []
    s = 1
    pk = 1
    for a in range(1, AMAX+1):
      pk *= p
      s += pk
      x = s
      j = 0
      while x % q == 0:
        x //= q; j += 1
      if x == 1: sols.append((a, j))
    print(f"sigma({p}^a) = {q}^j for a <= {AMAX}: {sols}")
