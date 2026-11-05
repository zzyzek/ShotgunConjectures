#!/usr/bin/env python3
# Generate tournament isomorphism-class representatives on k <= K vertices by
# one-vertex extension, with an explicit isomorphism for every extension
# (rep_i of k vertices + new vertex k with in-set S) -> rep_j of k+1 vertices;
# oriented-tree representatives on n vertices with maps from every
# "parent code"; and check that every tree rep embeds in every tournament rep
# on 2n-2 vertices.
#
# Tournament encoding: bit b(b-1)/2 + a (a < b) set  <=>  arc a -> b.
#
import sys, itertools, json

def tadj(t, a, b):
  if a < b:   return (t >> (b*(b-1)//2 + a)) & 1 == 1
  if b < a:   return (t >> (a*(a-1)//2 + b)) & 1 == 0
  return False

def ext_adj(t, S, k, a, b):
  if (a < k) and (b < k):  return tadj(t, a, b)
  if (b == k) and (a < k): return (S >> a) & 1 == 1
  if (a == k) and (b < k): return (S >> b) & 1 == 0
  return False

def encode(adj, k):
  t = 0
  for b in range(k):
    for a in range(b):
      if adj(a, b): t |= 1 << (b*(b-1)//2 + a)
  return t

def canon(adj, k):
  # Refine a vertex partition by out-degree into classes, then by counts of
  # out-neighbours per class; try all permutations within final cells.
  #
  col = [sum(1 for y in range(k) if adj(x, y)) for x in range(k)]
  while True:
    sig = [(col[x], tuple(sorted(col[y] for y in range(k) if adj(x, y)))) for x in range(k)]
    keys = sorted(set(sig))
    new = [keys.index(s) for s in sig]
    if len(set(new)) == len(set(col)):
      col = new
      break
    col = new
  cells = {}
  for x in range(k): cells.setdefault(col[x], []).append(x)
  order = sorted(cells)
  best = None
  for choice in itertools.product(*[itertools.permutations(cells[c]) for c in order]):
    seq = [x for cell in choice for x in cell]
    # new label of old vertex seq[i] is i; canon adj c(i,j) = adj(seq[i], seq[j])
    #
    t = encode(lambda i, j: adj(seq[i], seq[j]), k)
    if (best is None) or (t < best[0]): best = (t, seq)
  return best

def build(K):
  reps = {1: [0]}
  tables = {}
  for k in range(1, K):
    idx = {}
    nreps = []
    tab = []
    for i, t in enumerate(reps[k]):
      row = []
      for S in range(1 << k):
        c, seq = canon(lambda a, b: ext_adj(t, S, k, a, b), k+1)
        if c not in idx:
          idx[c] = len(nreps); nreps.append(c)
        j = idx[c]
        # pi(a) = seq[a]: ext_adj(pi a, pi b) = tadj(rep_j, a, b)
        #
        row.append((j, seq))
      tab.append(row)
    reps[k+1] = nreps
    tables[k] = tab
    print("k", k+1, "reps", len(nreps), file=sys.stderr)
  return reps, tables

# Oriented trees by parent codes: vertex i >= 1 has parent p[i] < i and an
# arc p[i] -> i if d[i] = 1, else i -> p[i].
#
def codes(n):
  for ps in itertools.product(*[range(i) for i in range(1, n)]):
    for ds in itertools.product([0, 1], repeat=n-1):
      arcs = []
      for i in range(1, n):
        p = ps[i-1]
        arcs.append((p, i) if ds[i-1] else (i, p))
      yield ps, ds, arcs

def tree_canon(arcs, n):
  A = set(arcs)
  best = None
  for perm in itertools.permutations(range(n)):
    # relabel old x -> perm[x]
    #
    key = tuple(sorted((perm[a], perm[b]) for a, b in A))
    if (best is None) or (key < best[0]): best = (key, perm)
  return best

def find_emb(arcs, n, adj, m):
  # Backtracking in index order; arcs only go between earlier/later vertices
  # of a parent code, so check each arc once both ends are placed.
  #
  f = [-1]*n
  used = [False]*m
  def go(i):
    if i == n: return True
    for x in range(m):
      if used[x]: continue
      ok = True
      for (a, b) in arcs:
        if (a == i) and (b < i) and (not adj(x, f[b])): ok = False; break
        if (b == i) and (a < i) and (not adj(f[a], x)): ok = False; break
      if not ok: continue
      f[i] = x; used[x] = True
      if go(i+1): return True
      used[x] = False
    return False
  return list(f) if go(0) else None

def tree_reps(n):
  reps = []
  idx = {}
  for ps, ds, arcs in codes(n):
    c = tree_canon(arcs, n)[0]
    if c not in idx:
      idx[c] = len(reps); reps.append(list(c))
  return reps

if __name__ == "__main__":
  N = int(sys.argv[1])
  M = 2*N - 2
  reps, tables = build(M)
  for n in range(2, N+1):
    m = 2*n - 2
    trs = tree_reps(n)
    bad = 0
    for t in reps[m]:
      for arcs in trs:
        if find_emb(arcs, n, lambda a, b: tadj(t, a, b), m) is None: bad += 1
    print("n", n, "tree reps", len(trs), "tournament reps", len(reps[m]), "failures", bad, file=sys.stderr)
