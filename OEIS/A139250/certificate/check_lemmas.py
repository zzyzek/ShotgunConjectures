# Toothpick CA (OEIS A139250): simulate with stages and check, on the structure
# inside the sealed box at stage 2^K, the statements of Lemmas 1-3, Theorem 1
# and Corollary 2 of ../README.md.  These lemmas are proved in the README; this
# script only checks that the definitions used there reproduce the sequence and
# that the proved statements hold on the data (a consistency check, not a proof).
#
# Usage: python3 check_lemmas.py K      (K <= 8 runs in seconds)
#
import sys
from collections import Counter

def simulate(N):
  # Toothpick = (cx, cy, d), d = 0 vertical, 1 horizontal; stage recorded.
  #
  occ, tps, last = Counter(), {}, []
  def place(c, d, s):
    tps[c] = (d, s)
    x, y = c
    for q in ([(x, y-1), c, (x, y+1)] if d == 0 else [(x-1, y), c, (x+1, y)]):
      occ[q] += 1
  place((0, 0), 0, 1); last = [((0, 0), 0)]
  counts = [1]
  for s in range(2, N+1):
    new = []
    for (c, d) in last:
      x, y = c
      for p in ([(x, y-1), (x, y+1)] if d == 0 else [(x-1, y), (x+1, y)]):
        if occ[p] == 1:
          new.append((p, 1-d))
    for (p, d) in new:
      place(p, d, s)
    last = new
    counts.append(len(tps))
  return tps, counts

def main():
  K = int(sys.argv[1]); N = 2**K
  tps, counts = simulate(N)
  A139250 = [1,3,7,11,15,23,35,43,47,55,67,79,95,123,155,171,175,183,195,207]
  assert counts[:20] == A139250, counts[:20]
  # Lemma 1: orientation and centre parity.
  #
  for (x, y), (d, s) in tps.items():
    assert d == (0 if s % 2 == 1 else 1)
    assert (x + y) % 2 == d
  # Lemma 2: no unit segment in two toothpicks.
  #
  seg = {}
  for (x, y), (d, s) in tps.items():
    for g in ([((x, y-1), (x, y)), ((x, y), (x, y+1))] if d == 0 else [((x-1, y), (x, y)), ((x, y), (x+1, y))]):
      assert g not in seg
      seg[g] = s
  # Lemma 3 inside the box |x| <= a-1, |y| <= a (a = 2^(K-1)), whose
  # interior and boundary are final at stage 2^K.
  #
  a = 2**(K-1)
  bad = 0
  for x in range(-(a-1), a):
    for y in range(-a, a+1):
      D = frozenset(dn for dn, (u, v) in (('E', (1, 0)), ('W', (-1, 0)), ('N', (0, 1)), ('S', (0, -1)))
                    if (min((x, y), (x+u, y+v)), max((x, y), (x+u, y+v))) in seg)
      if len(D) in (1,) or D in ({'N', 'E'}, {'N', 'W'}, {'S', 'E'}, {'S', 'W'}):
        bad += 1
  assert bad == 0
  # Theorem 1 and Corollary 2: holes (cell components not reaching the box
  # boundary) are rectangles; each side is covered by toothpicks of one stage.
  #
  def blocked(c, dn):
    x, y = c
    return {'R': ((x+1, y), (x+1, y+1)), 'L': ((x, y), (x, y+1)), 'U': ((x, y+1), (x+1, y+1)), 'D': ((x, y), (x+1, y))}[dn] in seg
  seen, holes, shapes = set(), 0, Counter()
  for sx in range(-(a-1), a-1):
    for sy in range(-a, a):
      if (sx, sy) in seen: continue
      comp, st = [(sx, sy)], [(sx, sy)]; seen.add((sx, sy))
      while st:
        x, y = st.pop()
        for dn, n in (('R', (x+1, y)), ('L', (x-1, y)), ('U', (x, y+1)), ('D', (x, y-1))):
          if blocked((x, y), dn) or n in seen: continue
          seen.add(n); comp.append(n); st.append(n)
      xs = [c[0] for c in comp]; ys = [c[1] for c in comp]
      x0, x1, y0, y1 = min(xs), max(xs)+1, min(ys), max(ys)+1
      if x0 < -(a-1) or x1 > a-1 or y0 < -a or y1 > a: continue
      holes += 1
      w, h = x1-x0, y1-y0
      assert w*h == len(comp)
      for side in ([seg[((x, y0), (x+1, y0))] for x in range(x0, x1)], [seg[((x, y1), (x+1, y1))] for x in range(x0, x1)],
                   [seg[((x0, y), (x0, y+1))] for y in range(y0, y1)], [seg[((x1, y), (x1, y+1))] for y in range(y0, y1)]):
        assert len(set(side)) == 1
      shapes[(min(w, h), max(w, h))] += 1
  print('K', K, 'stage', N, 'toothpicks', counts[-1], 'holes', holes, 'all checks passed')
  print('hole shapes (short side, long side): count', sorted(shapes.items()))

main()
