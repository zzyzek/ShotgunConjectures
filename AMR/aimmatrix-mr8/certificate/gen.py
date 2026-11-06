import itertools, sympy as sp
n = 7
TE = [(0,1),(1,2),(2,3),(3,4),(4,5),(4,6)]
adj = {i: set() for i in range(n)}
for a, b in TE: adj[a].add(b); adj[b].add(a)
def walk(r, i, j):
  if r == 0: return i == j
  return any(walk(r - 1, k, j) for k in adj[i])
def sp_(r): return {(i, j) for i in range(n) for j in range(n) if i != j and walk(r, i, j)}
G = {r: sp_(r) for r in (1, 2, 3, 4)}
for r in (1,2,3,4): print(r, sorted((i,j) for (i,j) in G[r] if i<j))

# lower bound: k x k submatrix, rows R cols C ordered so that all
# possibly-nonzero positions (edges or diagonal) below the diagonal are absent
# and the diagonal positions are edges.
#
def tri(Gr, k):
  pos = lambda u, v: (u == v) or ((u, v) in Gr)
  for R in itertools.permutations(range(n), k):
    for C in itertools.combinations(range(n), k):
      for Cp in itertools.permutations(C):
        if not all(((R[i], Cp[i]) in Gr) for i in range(k)): continue
        if all(not pos(R[i], Cp[j]) for i in range(k) for j in range(k) if j < i):
          return R, Cp
  return None
for r, k in ((1, 5), (2, 4), (3, 4)):
  print("tri", r, k, tri(G[r], k))

# upper bound for T: search small-integer diagonal, off-diagonal +-1 on edges.
#
best = None
for diag in itertools.product([-1, 0, 1], repeat=n):
  A = sp.zeros(n, n)
  for i in range(n): A[i, i] = diag[i]
  for (i, j) in G[1]: A[i, j] = 1
  if A.rank() == 5:
    best = A; break
print("T diag", best.diagonal() if best is not None else None)
