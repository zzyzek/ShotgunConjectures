# Check of the key step: n = 2k, pairs (a_r, b_r) r < k-1, extra points c, d.
# v = prod (e_a - e_b) at level k-1 on [2k]; beta = U^2 v (level k+1) lies in ker U;
# v' = same product on [2k] \ {c}; w = U v' lies in ker D^2 (level k on [2k] \ {c});
# <link_c beta, w> should be 2^k.  Also checks U beta = 0 and D^2 w = 0 directly.
import itertools, sys
def run(k):
  n = 2*k
  pairs = [(2*r, 2*r+1) for r in range(k-1)]
  c, d = n-2, n-1
  v = {}
  for choice in itertools.product((0, 1), repeat=k-1):
    T = frozenset(p[ch] for p, ch in zip(pairs, choice))
    v[T] = (-1)**sum(choice)
  def up(f, ground):
    g = {}
    for S, val in f.items():
      for x in ground:
        if x not in S:
          g[S | {x}] = g.get(S | {x}, 0) + val
    return {S: x for S, x in g.items() if x}
  def down(f):
    g = {}
    for S, val in f.items():
      for x in S:
        g[S - {x}] = g.get(S - {x}, 0) + val
    return {S: x for S, x in g.items() if x}
  G = range(n); Gc = [x for x in G if x != c]
  beta = up(up(v, G), G)
  assert not up(beta, G), 'beta not in ker U'
  w = up(v, Gc)
  assert not down(down(w)), 'w not in ker D^2'
  pairing = sum(val * w.get(S - {c}, 0) for S, val in beta.items() if c in S)
  return pairing
for k in range(1, 8):
  print(k, run(k), 2**k)
