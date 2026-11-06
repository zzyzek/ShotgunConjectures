import itertools
V = "abcdefg"
E3 = {frozenset(p) for p in ["ab","ad","cb","cd","cf","cg","eb","ed","ef","eg"]}
def pos(u, v): return (u == v) or (frozenset((u, v)) in E3)
res = []
for R in itertools.combinations(V, 4):
  for C in itertools.combinations(V, 4):
    ms = [p for p in itertools.permutations(C) if all(pos(R[i], p[i]) for i in range(4))]
    if len(ms) == 1 and all(R[i] != ms[0][i] for i in range(4)):
      res.append((R, C, ms[0]))
print(len(res)); print(res[:5])
