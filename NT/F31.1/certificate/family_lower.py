# Lower bound for k = 2*4^j + 5: no nonzero l in L with at most 2j-2 base-4 digits has k*l in L.
#
# k*l = 5*l + 2*4^j*l.  Write l = A + 4^j*B, A = digits a_0..a_{j-1} (a_0 != 0 after removing
# factors 4), B = digits b_0..b_{r-1} (r = number of digits of l minus j; r = 0 means B = 0).
# The balanced carry chain of k*l over positions has four consecutive segments:
#   positions 0..j-1      input 5*a_i                (pass 1)
#   positions j..j+r-1    input 5*b_i + 2*a_i        (pass 2)
#   positions j+r..2j-1   input 2*a_i                (pass 3, continues pass 2's carry)
#   positions 2j..2j+r-1  input 2*b_i                (pass 4)
# then zero inputs, so k*l in L iff every step has residue != 2 and the final carry is in
# {-1,0,1}.  Indexing all passes by i (digit index of A and B) runs them in lockstep: a finite
# automaton with state (c1, c2, c4, g1, g2): carries of passes 1, 2/3, 4 and the guessed initial
# carries g1 (= final carry of pass 1) and g2 (= final carry of pass 2/3).  Phase P (i < r) reads
# (a_i, b_i); phase Q (r <= i < j) reads a_i with pass 4 finished.  Accept at i = j iff c1 == g1,
# c2 == g2 and c4 in {-1,0,1}.  The script computes the reachable state sets for every phase-P
# length r (until the set sequence repeats) and, for each, every phase-Q length s (until repeat),
# and reports all (r, s) that accept.  "No acceptance with s >= 2" proves: l has >= 2j-1 digits.
#
D = (-1, 0, 1)
def st(x):
  r = x % 4
  if r == 2:
    return None
  b = {0: 0, 1: 1, 3: -1}[r]
  return (x - b) // 4
C = range(-2, 3)
def stepP(S, first, last):
  out = set()
  for (c1, c2, c4, g1, g2) in S:
    for a in D:
      if first and a == 0:
        continue
      for b in D:
        if last and b == 0:
          continue
        n1 = st(5*a + c1); n2 = st(5*b + 2*a + c2); n4 = st(2*b + c4)
        if None in (n1, n2, n4):
          continue
        out.add((n1, n2, n4, g1, g2))
  return frozenset(out)
def stepQ(S, first):
  out = set()
  for (c1, c2, c4, g1, g2) in S:
    for a in D:
      if first and a == 0:
        continue
      n1 = st(5*a + c1); n2 = st(2*a + c2)
      if None in (n1, n2):
        continue
      out.add((n1, n2, c4, g1, g2))
  return frozenset(out)
def accepts(S):
  return any(c1 == g1 and c2 == g2 and c4 in (-1, 0, 1) for (c1, c2, c4, g1, g2) in S)
init = frozenset((0, g1, g2, g1, g2) for g1 in C for g2 in C)
# For phase-P length r we need the set after r steps whose last b is nonzero; intermediate b free.
# Q_r = set after r P-steps with last b != 0 (r >= 1); Q_0 = init with c4 = g2 (B = 0).
def Pset(r):
  S = init
  for i in range(r):
    S = stepP(S, i == 0, i == r-1)
  return S
results = []
seenP = {}
# Free P-sets (b unrestricted) are eventually periodic; Pset(r) = last step from free set r-1.
free = [init]
r = 0
accept_pairs = []
while True:
  if r == 0:
    S0 = frozenset((0, g1, g2, g1, g2) for g1 in C for g2 in C)
  else:
    S0 = stepP(free[r-1], r-1 == 0, True)
  # Q-phase: first Q-step has the a_0 != 0 constraint only if r == 0.
  seenQ = {}
  S = S0; s = 0
  while True:
    key = (S, (r == 0) and (s == 0))
    if key in seenQ:
      break
    seenQ[key] = s
    if accepts(S):
      accept_pairs.append((r, s))
    S = stepQ(S, (r == 0) and (s == 0))
    s += 1
  qlen = s
  # extend free P sets
  nxt = stepP(free[r], r == 0, False)
  free.append(nxt)
  if nxt in free[1:-1] and r >= 3:
    rper = r
    break
  r += 1
  if r > 200:
    break
print('phase-P lengths examined up to r =', r + 1, ' (free set sequence repeats)')
print('accepting (r, s) pairs (r digits of B, s = j - r):', sorted(set(accept_pairs))[:40])
print('any with s >= 2:', [p for p in accept_pairs if p[1] >= 2])

# Cross-check against direct search: least digit count n(j) = j + r over accepting (r, s = j - r).
import subprocess
for j in range(1, 11):
  acc = []
  for r in range(0, j+1):
    S = Pset(r)
    for t in range(j - r):
      S = stepQ(S, (r == 0) and (t == 0))
    if accepts(S):
      acc.append(j + r)
  k = 2*4**j + 5
  out = subprocess.run(['./scripts/minm2', str(k), str(k)], capture_output=True, text=True).stdout.split()
  print('j', j, 'k', k, 'automaton least n', min(acc), 'direct search n', out[1])
