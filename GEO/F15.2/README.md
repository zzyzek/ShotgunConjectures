# CFG F15: worst-case shortest path through 4 points of the unit square is 3

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section F15. Paraphrase: for n points in the unit square let L(n) be the largest possible length of
the shortest polygonal path through all of them. The book asks for L(n) for small n and notes
L(2) = sqrt 2, L(3) = (2 + sqrt 5)/2.

**Result (partial).** L(4) = 3, attained by the four corners. Numerically L(5) = 2 + sqrt 2
(corners and centre); not proved here. L(n) for n >= 5 remains open in this repository.

**Argument for n = 4.** Lower bound: through the four corners every path has three edges of
length at least 1. Upper bound, for points A, B, C, D in [0,1]^2:
- *Collinear points:* the path along the line has length at most sqrt 2.
- *Convex position (hull a quadrilateral):* the hull boundary is a closed tour of length p, and
  p <= 4 because a convex polygon inside the square has perimeter at most that of the square
  (standard: cut the square along the lines of the polygon's sides; each cut shortens the
  perimeter by the triangle inequality). Deleting the longest of the four tour edges leaves a path
  of length at most 3p/4 <= 3.
- *One point inside the triangle of the others:* let D lie in triangle XYZ with sides
  a <= b <= c and perimeter P. For each side UV of the triangle take the path U-D-V-W or V-D-U-W
  (W the third vertex, ending with the shorter of |UW|, |VW|). Its length is |DU| + |DV| plus the
  shorter remaining side. Summing over the three sides gives 2S + (a + a + b), where
  S = |DX| + |DY| + |DZ|. S is convex in D, so on the triangle it is at most its value at a vertex,
  at most b + c. The shortest of the three paths is therefore at most
  (2(b + c) + 2a + b)/3 = (2P + b)/3. The perimeter of a triangle in the square is convex in each
  vertex, so P <= 2 + sqrt 2 (three corners), and b <= sqrt 2. Hence the path is at most
  (4 + 3 sqrt 2)/3 < 2.75 < 3.

**Evidence.**
- `certificate/opt.py`: random-restart hill climbing for n = 3, 4, 5 gives 2.11803 = (2 + sqrt 5)/2,
  3.0 (corners) and 3.41410 (corners and centre).
- `certificate/check4.py`: 200000 random triangles with an inner point; the bound (2P + b)/3 is never
  below the true shortest path and never above 2.4245.
- No Lean. Outside Lean: the whole argument (including the perimeter monotonicity for convex
  polygons, which is standard but not formalised).

**Review level.** `agent`.

**What blocks n = 5.** With hull a quadrilateral and one inner point, the extremal configuration
(corners and centre) is tight, so averaging bounds must be exact there; the natural bound (insert
the inner point into the side of the diagonal triangle containing it, drop the two adjacent sides'
neighbours) fails for thin quadrilaterals (value up to 5.6 numerically), so a case split by hull
shape is needed.

**Prior art.** Checked 2026-11-06: web searches for small-n values of the longest shortest path
(open TSP path) in the unit square; Balogh, Clemen, Dumitrescu, arXiv:2310.02839 (squared lengths,
not this question); Moran 1984 (unit-diameter sets). No statement of L(4) = 3 found, but the case is
easy and may be folklore. Not in google-deepmind/formal-conjectures (grep "shortest path" finds
only unrelated graph conjectures).
