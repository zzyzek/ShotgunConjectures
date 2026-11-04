# Count, for random perfect squared rectangles, the squares not touching the
# boundary all of whose edge-neighbours are larger (permissive count).  A
# rectangle with count <= 1 answers Moron's first question (C2) negatively
# under any reading of 'surrounded'.  Also stores rectangles for GEO-C2.3.
#
import sys, random, time, json
sys.path.insert(0, sys.argv[3])
from gen import random_graph, squared, valid_tiling
def surrounded(sq, W, H):
  out = []
  for s, x, y in sq:
    if x == 0 or y == 0 or x + s == W or y + s == H:
      continue
    ok = True
    for t, u, v in sq:
      if (t, u, v) == (s, x, y):
        continue
      vert = (u + t == x or x + s == u) and min(y + s, v + t) - max(y, v) > 0
      horz = (v + t == y or y + s == v) and min(x + s, u + t) - max(x, u) > 0
      if (vert or horz) and t < s:
        ok = False; break
    if ok:
      out.append(s)
  return out
rnd = random.Random(int(sys.argv[1])); T = float(sys.argv[2])
t0 = time.time(); seen = {}; hist = {}; bad = []
while time.time() - t0 < T:
  nv = rnd.randint(6, 11)
  g = random_graph(rnd, nv, rnd.randint(0, 2 * nv))
  if g is None:
    continue
  nv, E, left, find = g
  for bat in rnd.sample(E, min(3, len(E))):
    r = squared(nv, E, left, find, bat)
    if r is None:
      continue
    sq, W, H = r
    sizes = sorted(a for a, _, _ in sq)
    if len(set(sizes)) != len(sizes):
      continue
    key = (tuple(sizes), min(W, H), max(W, H))
    if key in seen:
      continue
    assert valid_tiling(sq, W, H), (sq, W, H)
    seen[key] = sq
    c = surrounded(sq, W, H)
    hist[len(c)] = hist.get(len(c), 0) + 1
    if len(c) <= 1:
      bad.append((W, H, sq, c))
print("perfect rectangles", len(seen), "hist of permissive count", dict(sorted(hist.items())))
for W, H, sq, c in bad[:5]:
  print("COUNT<=1:", W, H, "order", len(sq), "surrounded", c, "squares", sorted(sq))
json.dump([[list(k[0]), k[1], k[2], v] for k, v in seen.items()], open(sys.argv[4], "w"))
