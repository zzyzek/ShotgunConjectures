# Croft, Falconer, Guy, Unsolved Problems in Geometry

H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991. Statements are paraphrased with the section number.

12 entries: 5 resolved by this project, 4 answered elsewhere, 3 disputed or partial.

Of the 5 resolutions: 3 proved in full in Lean, 0 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 2 on paper only (re-derived by a second reader; 2 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Resolved by this project

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [C2.1](C2.1/) | disproved | a perfect squared rectangle with only one square surrounded by larger ones | [full proof](C2.1/C2_1_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [C2.2](C2.2/) | disproved | a coprime perfect squared rectangle with no square of square side | [full proof](C2.2/C2_2_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C2.3](C2.3/) | proved | a rectangle with two perfect squarings sharing no square size | [full proof](C2.3/C2_3_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [E4.4](E4.4/) | proved | Birch's 8-point question holds for points in general position | needs Mathlib | new | [elementary-proof](../methods/elementary-proof/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [F3.5](F3.5/) | trivial or misstated | order of magnitude of g\_d(n), the largest n-distance set in R^d | needs Mathlib | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A19.1](A19.1/) | trivial or misstated | minimal perimeter of a plane convex set of given diameter and width | — | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [B18.2](B18.2/) | proved | every polyhedron has a realization with all edges tangent to a sphere | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [F5.1](F5.1/) | proved | lim f\_3(n)/n^(1/3), minimum diameter of n points in R^3 with minimum distance 1 | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [density-bound](../methods/density-bound/README.md) |
| [F16.2](F16.2/) | known | the thrackle conjecture for small n | — | known | [known-theorem](../methods/known-theorem/README.md) |

## Disputed or only partly answered (not counted as resolutions)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [B15.1](B15.1/) | proved | counting polyhedra by vertices and faces — not a resolution | — | — | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [B17.1](B17.1/) | proved | smallest dimension of a simplicial polytope with non-unimodal f-vector is 20 | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [D5.4](D5.4/) | proved | rectangles of total area 1 and side ≤ 1 pack into a square of area 2 | — | — | [known-theorem](../methods/known-theorem/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

### [C2.1](C2.1/): a perfect squared rectangle with only one square surrounded by larger ones

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section C2. Moroń asked whether in a squared rectangle there are always at
least two squares that are surrounded by (four) larger ones. ("Probably not.")

**Reading.** "Squared rectangle" read as perfect (all squares different); with repeated sizes
even a 2 × 1 rectangle of two unit squares has none. A square counts as surrounded (most
permissive reading) if it does not touch the boundary and every square sharing a boundary
segment of positive length with it is larger; every stricter reading gives a smaller count.
Moroń's original wording (Colloq. Math. 2 (1951) Problems 66–68) was not seen.

**Result.** No. The classical order-9 perfect rectangle 61 × 69 with squares 2, 5, 7, 9, 16,
25, 28, 33, 36 has exactly one surrounded square (side 2). (The smallest square of a perfect
squared rectangle is always surrounded, so 1 is the least possible count.)

**Argument.** The four squares not touching the boundary are 2, 5, 7, 9; each of 5, 7, 9 shares
an edge segment with the square 2 (along y = 36, x = 38, y = 34 respectively), so only 2 is
surrounded.

Lean: [full proof](C2.1/C2_1_mathlib.lean).

### [C2.2](C2.2/): a coprime perfect squared rectangle with no square of square side

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section C2. Moroń asked whether, in a squared rectangle whose sides are
relatively prime, there is always a square whose side is a perfect square. ("Probably not.")

**Result.** No. The simple perfect squared rectangle 799 × 689 (gcd 1) of order 14 with squares
5, 7, 23, 28, 30, 37, 44, 67, 72, 220, 287, 292, 397, 402 has no square whose side is a perfect
square. (The scan also found witnesses of orders 17 and 23.)

**Argument.** Direct check of the tiling and of the 14 sides.

Lean: [full proof](C2.2/C2_2_mathlib.lean).

### [C2.3](C2.3/): a rectangle with two perfect squarings sharing no square size

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section C2. Moroń asked whether some rectangle can be squared in two distinct
ways with no square occurring in both squarings. ("Probably so.")

**Result.** Yes. The 593 × 422 rectangle has the perfect squarings
{2, 22, 37, 39, 41, 43, 80, 164, 178, 200, 207, 215, 222} and
{18, 38, 49, 67, 72, 85, 103, 116, 154, 175, 192, 230, 247}, both of order 13, with no common
size.

**Argument.** Direct check of both tilings.

Lean: [full proof](C2.3/C2_3_mathlib.lean).

### [E4.4](E4.4/): Birch's 8-point question holds for points in general position

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section E4. Birch asks whether every set of 8 points in the plane can be
partitioned into two triangles and a segment so that the segment cuts the interior of both
triangles.

**Reading.** "Triangle" = convex hull of three of the points; "cuts the interior" = the segment
meets the open triangle.

**Result.** - Points in general position (no three collinear): yes.
- As literally stated, for arbitrary sets: no. With 7 collinear points and one more, a triangle
  with nonempty interior must use the off-line point, so two such triangles cannot coexist.

**Argument.** For points in general position the property depends only on the orientations of
triples. Sort the points by x-coordinate (after a rotation). The orientations form a signotope
(for i < j < k < l the sequence χ(ijk), χ(ijl), χ(ikl), χ(jkl) changes sign at most once), so a
SAT encoding over all signotopes covers every general-position set (and possibly non-realizable
ones, which only strengthens UNSAT). "Segment pq meets open triangle abc" is exact in general
position as: p or q strictly inside, or pq properly crossing an edge. Forbidding all 280
partitions is UNSAT.

Lean: needs Mathlib.

### [F3.5](F3.5/): order of magnitude of g_d(n), the largest n-distance set in R^d

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section F3. g_d(n) is the largest number of points in R^d determining at most
n distinct distances. Bannai, Bannai & Stanton and Blokhuis showed g_d(n) ≤ C(d + n, n); the book
asks whether "g_d(n) ~ d^n is the correct order of magnitude for large n" (our copy's wording).

**Reading.** Two readings, both trivial.
- d → ∞ with n fixed (the reading in which d^n is natural): yes, g_d(n) = Θ_n(d^n).
- n → ∞ with d fixed (literal "for large n"): no, since C(d + n, n) = C(n + d, d) is a
  polynomial of degree d in n, far below d^n.

**Result.** Trivial or misstated (see Reading).

**Argument.** Upper bound: C(d + n, n) ≤ (d + n)^n / n! = (1 + o(1)) d^n / n! as d → ∞. Lower
bound: the 0/1 vectors of length d + 1 with exactly n ones lie in the hyperplane Σx_i = n
(a copy of R^d), number C(d + 1, n) = (1 + o(1)) d^n / n!, and their pairwise distances are
√(2j), 1 ≤ j ≤ n, so at most n distances (for d + 1 ≥ 2n; otherwise use fewer ones). Hence
g_d(n) ≍ d^n / n! for fixed n.

Lean: needs Mathlib.

### [A19.1](A19.1/): minimal perimeter of a plane convex set of given diameter and width

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991), A19
"Extremal problems for elongated sets". Paraphrase: Bieri asks for the least perimeter of a plane
convex set with given diameter d and (minimal) width w; the book reports a conjecture that the
extremal sets are polygons inscribed in a Reuleaux triangle, and calls the other three problems of
this type (largest perimeter, least and largest area) routine. Cited source: H. Bieri, Problems 5
and 6 in [TW] p. 256, i.e. P. M. Gruber and R. Schneider, Problems in geometric convexity, in
J. Tölke and J. M. Wills (eds.), *Contributions to Geometry*, Birkhäuser 1979, 255-278.

**Reading.** The scan's text of the book (`text/unsolved_geom.txt` in the scan repository) has only
the CFG paragraph above and the citation; Bieri's own wording in [TW] was not consulted. The answer
below is for the question as CFG print it. If CFG garbled a different problem of Bieri's (for example
one with a further constraint), this write-up does not address it.

**Result.** Misstated. As printed the problem is classical and the conjectured extremals are wrong.
For 0 < w <= d the least perimeter is p = 2 sqrt(d^2 - w^2) + 2 w arcsin(w/d), attained by the convex
hull of a disk of diameter w and the two ends of a segment of length d through its centre. No polygon
attains it.

**Argument.** Let b(t) be the width in direction t. Cauchy's formula gives p = integral over [0, pi)
of b(t) dt. By definition of the width, b(t) >= w. If x, y are the ends of a diameter, in direction
t0, then the projection of the segment xy gives b(t) >= d |cos(t - t0)|. So
p >= integral of max(w, d |cos s|) ds over s in [0, pi). With alpha = arccos(w/d) the integrand is
d |cos s| on |s| < alpha (mod pi) and w elsewhere, so the integral is
2 d sin(alpha) + w (pi - 2 alpha) = 2 sqrt(d^2 - w^2) + 2 w arcsin(w/d).
The hull K of the disk of radius w/2 centred at 0 and the points ±(d/2) e has support function
h(s) = max(w/2, (d/2) |cos s|) (angle s from e), so its width is max(w, d |cos s|): K has width w,
diameter d, and equality holds. Any extremal set must have b(t) = w on an interval of directions of
length pi - 2 alpha > 0 (for w = d, on all directions). The width function of a polygon is, piece by
piece, c |cos(t - phi)| with c > 0 (the projection of a pair of vertices), which is never constant on
an interval, so no polygon is extremal. Checks: w = d gives pi d (Barbier); w -> 0 gives 2d.

Lean: —.

### [B18.2](B18.2/): every polyhedron has a realization with all edges tangent to a sphere

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section B18. Is every convex polyhedron combinatorially equivalent to one with
all its edges touching a sphere?

**Result.** Yes: the Koebe–Andreev–Thurston circle packing theorem in its midsphere form
(every 3-connected planar graph is realized by a polyhedron whose edges are tangent to the unit
sphere; one can even choose the realization with the origin as centroid of the tangency
points). Literature answer, not a scan resolution.

**Argument.** Not reproduced (circle-packing theorem).

Lean: —.

### [F5.1](F5.1/): lim f_3(n)/n^(1/3), minimum diameter of n points in R^3 with minimum distance 1

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section F5. f_d(n) is the least diameter of a set of n points in R^d with minimum mutual distance 1.
The book quotes Thue's planar result lim f_2(n)/n^(1/2) = 2^(1/2) 3^(1/4) pi^(-1/2) and says the
value of lim f_3(n)/n^(1/3) is unsolved, related to optimal ball-packing density.

**Result.** Known (immediate consequence of the Kepler conjecture, proved by Hales):

lim f_3(n)/n^(1/3) = (3 sqrt2 / pi)^(1/3) = (6/(sqrt2 pi))^(1/3) = 1.10533...

**Argument.** Write delta = sqrt2, the point density of the face-centred cubic (fcc) lattice with
minimum distance 1 (cubic cell of side sqrt2 holding 4 points). Kepler (Hales): every packing of
balls of radius 1/2 in R^3 has density at most pi/sqrt18 = delta * (pi/6).

*Upper bound.* Let c be the circumradius of the Voronoi cell of the fcc lattice. The Voronoi cells
of the lattice points in the closed ball B(0, R) cover B(0, R - c), so B(0, R) holds at least
delta (4 pi/3)(R - c)^3 lattice points. Any n of them form a set with minimum distance 1 and
diameter at most 2R. Taking the least R with delta (4 pi/3)(R - c)^3 >= n gives
f_3(n) <= (6n/(delta pi))^(1/3) + O(1).

*Lower bound.* Let P be n points with minimum distance 1 and diameter D, K its convex hull
(diameter D). Fix s > 0 and cut R^3 into cubes of side s.
- A single cube Q: the balls of radius 1/2 around P cap Q lie in a cube of side s + 1. Repeating
  that cube periodically with period s + 1 gives a packing of density
  |P cap Q| (pi/6) / (s + 1)^3, so Kepler gives |P cap Q| <= delta (s + 1)^3.
- Cubes that meet K lie in K + B(0, s sqrt3), a set of diameter at most D + 2 sqrt3 s. By the
  isodiametric inequality its volume is at most pi (D + 2 sqrt3 s)^3 / 6, so at most that
  volume divided by s^3 cubes meet K.
Hence n <= delta (pi/6) (1 + 1/s)^3 (D + 2 sqrt3 s)^3. With s = sqrt D this is
n <= delta (pi/6) D^3 (1 + O(D^(-1/2))), so f_3(n) >= (6n/(delta pi))^(1/3) (1 - o(1)).

Both bounds give the limit (6/(sqrt2 pi))^(1/3). The same argument in the plane, with Thue's
hexagonal density 2/sqrt3, reproduces the book's planar constant 2^(1/2) 3^(1/4) pi^(-1/2).

Lean: needs Mathlib.

### [F16.2](F16.2/): the thrackle conjecture for small n

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section F16. A thrackle is a drawing of a graph in the plane in which every pair of edges meets
exactly once, either at a common endpoint or at a proper crossing. Conway's thrackle conjecture
says a thrackle on n vertices has at most n edges. The book notes experimental evidence near
n = 10 and asks whether there is at least a proof for small n.

**Result.** Known. The thrackle conjecture holds for every graph with at most 12 vertices
(J. Pammer 2014, by enumerating path-thrackles). The bound n <= 11 was used earlier as a known
fact (Goddyn and Xu 2017). The general conjecture is open.

**Argument.** Computer enumeration in the cited thesis; not re-derived here.

Lean: —.

### [B15.1](B15.1/): counting polyhedra by vertices and faces — not a resolution

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section B15. How many combinatorially different convex polyhedra have v
vertices and f faces? The book notes exact values are known only for small v, f (its Table B1),
asks for a significantly more efficient enumeration algorithm than extending the table, for the
computational complexity, and for asymptotics.

**Result.** Disputed as a resolution. Fast generators exist (plantri, Brinkmann & McKay 2007,
enumerates 3-connected planar graphs far beyond Table B1; counts by edges are OEIS A000944),
so the table has been extended. But the book's questions (an exact count in general, a provably
better algorithm, the complexity, asymptotics for unrooted polyhedra) are open-ended and are
not settled by that. The scan's record cites plantri and OEIS from memory.

**Argument.** None.

Lean: —.

### [B17.1](B17.1/): smallest dimension of a simplicial polytope with non-unimodal f-vector is 20

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section B17. Björner and Lee found simplicial polytopes with non-unimodal
f-vectors in dimensions 24 and 20; the book asks for the smallest dimension in which
unimodality fails, both for simplicial polytopes and in general (Björner: true for simplicial
d ≤ 15).

**Result.** Simplicial case: 20. Eckhoff showed that simplicial d-polytopes have unimodal
f-vectors for d ≤ 19, and the 20-dimensional examples of Björner and of Lee are non-unimodal.
Literature answer. The general (non-simplicial) case asked in the same sentence is not settled
by this record.

**Argument.** None beyond the citations.

Lean: —.

### [D5.4](D5.4/): rectangles of total area 1 and side ≤ 1 pack into a square of area 2

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section D5. Can every set of rectangles with total area 1 and maximum side 1
be packed into a square of area 2? If they have total area 3 and maximum side 1, will they
cover a square of area 1?

**Result.** Packing question: yes, according to the introduction of a paper in Periodica
Mathematica Hungarica (doi 10.1007/s10998-015-0083-2, 2015), which states the answer is positive
and cites an earlier reference that was not identified. Covering question: not checked.
Literature, partial.

**Argument.** None.

Lean: —.

