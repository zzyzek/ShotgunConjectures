import sys, itertools
import networkx as nx

# Strict power: ij edge iff some walk of length exactly r joins i != j.
# In a tree this means dist(i,j) <= r and dist(i,j) = r (mod 2).
#
def strict_power(T, r, d):
  G = nx.Graph()
  G.add_nodes_from(T.nodes())
  for i, j in itertools.combinations(T.nodes(), 2):
    if ( (d[i][j] <= r) and ((d[i][j] % 2) == (r % 2)) ):
      G.add_edge(i, j)
  return G

# Zero forcing number of a connected graph by increasing subset size.
#
def zf_closure(nb, S, n):
  black = set(S)
  changed = True
  while changed:
    changed = False
    for v in list(black):
      w = [u for u in nb[v] if u not in black]
      if len(w) == 1:
        black.add(w[0])
        changed = True
  return len(black) == n

def zf(G):
  nodes = list(G.nodes())
  n     = len(nodes)
  nb    = {v: list(G.neighbors(v)) for v in nodes}
  for k in range(1, n + 1):
    for S in itertools.combinations(nodes, k):
      if zf_closure(nb, S, n):
        return k
  return n

# Clique (edge) cover number, exact, by branching on an uncovered edge.
#
def cc(G):
  edges = [frozenset(e) for e in G.edges()]
  if not edges:
    return 0
  cl    = [frozenset(c) for c in nx.find_cliques(G) if len(c) >= 2]
  best  = [len(edges)]
  def rec(unc, used):
    if used >= best[0]:
      return
    if not unc:
      best[0] = used
      return
    e = next(iter(unc))
    for c in cl:
      if e <= c:
        rec({f for f in unc if not (f <= c)}, used + 1)
  rec(set(edges), 0)
  return best[0]

# Bounds on mr summed over components: lb = |C| - Z(C), ub = cc(C)
# (isolated vertex contributes 0).
#
def bounds(G):
  lb = 0
  ub = 0
  for C in nx.connected_components(G):
    H = G.subgraph(C)
    if len(C) == 1:
      continue
    lb += len(C) - zf(H)
    ub += cc(H)
  return lb, ub

nmax = int(sys.argv[1])
for n in range(4, nmax + 1):
  for T in nx.nonisomorphic_trees(n):
    if max(dict(T.degree()).values()) == (n - 1):
      continue
    d    = dict(nx.all_pairs_shortest_path_length(T))
    diam = max(max(x.values()) for x in d.values())
    seq  = []
    for r in range(1, diam + 2):
      seq.append(bounds(strict_power(T, r, d)))
    exact = all(a == b for a, b in seq)
    # Violation: some r with mr(r) > 2 and mr(r+1) >= mr(r) certified
    # by lb(r+1) >= ub(r) > 2.
    #
    viol = [r + 1 for r in range(len(seq) - 1) if ( (seq[r][1] > 2) and (seq[r + 1][0] >= seq[r][1]) )]
    unsure = [r + 1 for r in range(len(seq) - 1) if ( (seq[r][1] > 2) and (seq[r + 1][0] < seq[r][1]) and (seq[r + 1][1] >= seq[r][0]) and (seq[r][0] > 2) )]
    inc = [r + 1 for r in range(len(seq) - 1) if ( (seq[r][1] > 2) and (seq[r + 1][0] > seq[r][1]) )]
    if inc:
      print("INC", n, sorted(T.edges()), seq, inc, flush=True)
    if viol and (n <= 8):
      print(n, sorted(T.edges()), seq, "VIOL" if viol else "", viol, "UNSURE" if unsure else "", "" if exact else "GAP", flush=True)
