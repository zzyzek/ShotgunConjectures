# Controls for om.py: (1) count signotopes for n=3..6 (expect 2, 8, 62, 908);
# (2) with 'hit' weakened to 'an endpoint is inside', 8 points must be SAT
# (convex position has no point inside any triangle).
#
import itertools, sys
from pysat.solvers import Cadical153
def base(n):
  ids = {t: i + 1 for i, t in enumerate(itertools.combinations(range(n), 3))}
  C = []
  for i, j, k, l in itertools.combinations(range(n), 4):
    seq = [ids[(j, k, l)], ids[(i, k, l)], ids[(i, j, l)], ids[(i, j, k)]]
    for x, y, z in itertools.combinations(range(4), 3):
      C.append([-seq[x], seq[y], -seq[z]]); C.append([seq[x], -seq[y], seq[z]])
  return ids, C
for n in range(3, 7):
  ids, C = base(n)
  cnt = 0
  with Cadical153(bootstrap_with=C) as S:
    while S.solve():
      m = S.get_model()[:len(ids)]
      cnt += 1
      S.add_clause([-v for v in m])
  print("n=%d signotopes=%d" % (n, cnt))
