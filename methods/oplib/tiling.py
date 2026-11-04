"""
Integer tilings of rectangles by squares (and boxes): checks and searches.

Pattern. Questions about squared rectangles (Moron, Brooks-Smith-Stone-Tutte)
are answered by generating many perfect squared rectangles and filtering. The
generator is electrical: a 3-connected planar graph with a battery across one
edge gives Kirchhoff currents = square sides and potentials = coordinates
(exact rationals, scaled to integers). See work/GEO-C2.1/gen.py (needs scipy
for the random triangulation); the checks here are dependency-free.

Used for: GEO-C2.1, C2.2, C2.3 (Moron's three questions), GEO-C5.3
(incomparable cuboids: SAT encoding instead, see oplib.sat).
"""
from math import gcd


def check_tiling(W, H, squares):
  """squares: list of (s, x, y). True if they tile the W x H rectangle exactly
  (inside, pairwise disjoint interiors, total area W*H)."""
  for s, x, y in squares:
    if (x < 0) or (y < 0) or (x + s > W) or (y + s > H):
      return False
  for i in range(len(squares)):
    s, x, y = squares[i]
    for t, u, v in squares[i + 1:]:
      if not ( (x + s <= u) or (u + t <= x) or (y + s <= v) or (v + t <= y) ):
        return False
  return sum(s * s for s, _, _ in squares) == W * H


def is_perfect(squares):
  """All square sizes distinct."""
  sides = [s for s, _, _ in squares]
  return len(sides) == len(set(sides))


def neighbours(squares):
  """Edge-adjacency (shared boundary segment of positive length) as index lists."""
  nb = [[] for _ in squares]
  for i, (s, x, y) in enumerate(squares):
    for j, (t, u, v) in enumerate(squares):
      if i == j:
        continue
      vert = ( (x + s == u) or (u + t == x) ) and (max(y, v) < min(y + s, v + t))
      horz = ( (y + s == v) or (v + t == y) ) and (max(x, u) < min(x + s, u + t))
      if vert or horz:
        nb[i].append(j)
  return nb


def surrounded(W, H, squares):
  """Indices of interior squares all of whose edge-neighbours are larger."""
  nb = neighbours(squares)
  out = []
  for i, (s, x, y) in enumerate(squares):
    border = (x == 0) or (y == 0) or (x + s == W) or (y + s == H)
    if (not border) and all(squares[j][0] > s for j in nb[i]):
      out.append(i)
  return out


def lean_list(name, squares):
  """Lean `def name : List Sq := [...]` for oplib.lean / lean/Rectangles.lean."""
  body = ', '.join('⟨%d, %d, %d⟩' % q for q in squares)
  return 'def %s : List Sq :=\n  [%s]\n' % (name, body)


def reduced(W, H):
  g = gcd(W, H)
  return (W // g, H // g)
