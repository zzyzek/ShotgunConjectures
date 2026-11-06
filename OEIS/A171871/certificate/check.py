# Count codes (sets of N words in {0,1}^R) up to the hypercube group, all
# codes (A039754) and those that are classifications (A171871 reading:
# columns nonconstant, pairwise neither equal nor complementary, every
# column needed to separate the words).
import itertools, sys
def run(R):
  W = list(range(1 << R))
  G = []
  for p in itertools.permutations(range(R)):
    for m in range(1 << R):
      G.append([sum((((w >> p[i]) & 1) << i) for i in range(R)) ^ m for w in W])
  seen = {}
  for mask in range(1 << (1 << R)):
    C = [w for w in W if (mask >> w) & 1]
    canon = min(sum(1 << g[w] for w in C) for g in G)
    if canon != mask:
      continue
    N = len(C)
    ok = True
    for i in range(R):
      col = [(w >> i) & 1 for w in C]
      if len(set(col)) < 2: ok = False
      for j in range(i):
        cj = [(w >> j) & 1 for w in C]
        if cj == col or cj == [1 - x for x in col]: ok = False
      dele = [w & ~(1 << i) for w in C]
      if len(set(dele)) == N: ok = False
    seen.setdefault(N, [0, 0])
    seen[N][0] += 1
    if ok: seen[N][1] += 1
  return seen
for R in range(0, 5):
  s = run(R)
  print("R=%d" % R, " ".join("N%d:%d/%d" % (N, s[N][1], s[N][0]) for N in sorted(s)))
