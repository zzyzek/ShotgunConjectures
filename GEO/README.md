# Croft, Falconer, Guy, Unsolved Problems in Geometry

H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991. Statements are paraphrased with the section number.

27 entries: 7 resolved by this project, 9 answered elsewhere, 5 disputed or partial.

Of the 7 resolutions: 3 proved in full in Lean, 1 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 3 on paper only (re-derived by a second reader; 1 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Resolved by this project

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [B22.2](B22.2/) | disproved | no convex polyhedron has all faces directly congruent to a right or obtuse scalene triangle | [witness](B22.2/B22_2.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [C2.1](C2.1/) | disproved | a perfect squared rectangle with only one square surrounded by larger ones | [full proof](C2.1/C2_1_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [C2.2](C2.2/) | disproved | a coprime perfect squared rectangle with no square of square side | [full proof](C2.2/C2_2_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C2.3](C2.3/) | proved | a rectangle with two perfect squarings sharing no square size | [full proof](C2.3/C2_3_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C5.2](C5.2/) | disproved | incomparable tilings cannot have all tiles close to squares | — | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [E4.4](E4.4/) | proved | Birch's 8-point question holds for points in general position | [checked](E4.4/E4_4_lrat.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [F3.5](F3.5/) | trivial or misstated | order of magnitude of g\_d(n), the largest n-distance set in R^d | needs Mathlib | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A12.2](A12.2/) | disproved | Fickett's cosecant bound for congruent triangles is false | [witness](A12.2/A12_2.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A19.1](A19.1/) | trivial or misstated | minimal perimeter of a plane convex set of given diameter and width | — | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A33.2](A33.2/) | disproved | the Lamé oval \|x\|^2.001 + \|y\|^2.001 = 1 has five-point hyperbolas | — | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [B18.2](B18.2/) | proved | every polyhedron has a realization with all edges tangent to a sphere | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [C1.3](C1.3/) | answered | repeated subdivision of tetrahedra with a(T)/r(T) bounded (Hajós) | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [C3.1](C3.1/) | known | Mrs Perkins's quilt, f(n) beyond 100 and Selfridge's prime sets | — | known | [reading-the-statement](../methods/reading-the-statement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C10.2](C10.2/) | proved | the plane can be tiled with exactly one square of each positive rational side | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [F5.1](F5.1/) | proved | lim f\_3(n)/n^(1/3), minimum diameter of n points in R^3 with minimum distance 1 | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [density-bound](../methods/density-bound/README.md) |
| [F16.2](F16.2/) | known | the thrackle conjecture for small n | — | known | [known-theorem](../methods/known-theorem/README.md) |

## Disputed or only partly answered (not counted as resolutions)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [B15.1](B15.1/) | proved | counting polyhedra by vertices and faces — not a resolution | — | — | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [B17.1](B17.1/) | proved | smallest dimension of a simplicial polytope with non-unimodal f-vector is 20 | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [C16.3](C16.3/) | partial | settled order by order up to n = 25; no general rule | — | known | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [D5.4](D5.4/) | proved | rectangles of total area 1 and side ≤ 1 pack into a square of area 2 | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [F13.2](F13.2/) | partial | n non-collinear points determine at least n-2 angles, proved for large n | — | known | [known-theorem](../methods/known-theorem/README.md) |

## Weaker results on open problems (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A4.4](A4.4/) | partial | billiards in the regular tetrahedron — every periodic orbit has even period | [full proof](A4.4/A4_4.lean) | new | [modular-obstruction](../methods/modular-obstruction/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [C8.2](C8.2/) | partial | more than 120 congruent "non-thin" triangles on the sphere? | — | partly-known | [known-theorem](../methods/known-theorem/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [F9.1](F9.1/) | partial | nine points with 19 unit circles through three of them, so f(9) ≥ 19 | [witness](F9.1/F9_1.lean) | new | [finite-witness-counterexample](../methods/finite-witness-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [F15.2](F15.2/) | partial | worst-case shortest path through 4 points of the unit square is 3 | — | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [F17.3](F17.3/) | partial | maximum-volume polyhedron with 10 vertices on the unit sphere | — | partly-known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [G9.2](G9.2/) | partial | two sets always meeting in exactly n points — odd n is impossible for curve-like sets | — | new | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

### [B22.2](B22.2/): no convex polyhedron has all faces directly congruent to a right or obtuse scalene triangle

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer
1991, problem B22 (paraphrase): for which triangles T is there a convex polyhedron all of whose
faces are congruent to T, with or without reflections allowed; how many faces, and how arranged?
The scan item B22.2 is the orientation-preserving case ("directly congruent", no reflections)
for the triangles left open by arXiv:2608.01109: right and obtuse scalene triangles.

**Reading.** Faces are the facets of a convex polyhedron in R³; "directly congruent" means
congruent by an orientation-preserving isometry, with each face viewed from outside the polyhedron.

**Result.** For a scalene triangle T, every convex polyhedron whose faces are all directly
congruent to T is a tetrahedron with one corner of each angle of T at every vertex (a
disphenoid). Such a tetrahedron exists only when T is acute. Hence for right and obtuse scalene
triangles the answer is no, and for acute scalene triangles the disphenoid (4 faces) is the only
example.

**Argument.** Let T have sides a, b, c (distinct) with opposite angles A, B, C.
1. Edge to edge. Each face is a triangle, its sides are edges of the polyhedron, and each edge
   lies in exactly two faces. Since T is scalene, every edge has a well-defined label a, b or c
   (its length), the same in both faces.
2. Same cyclic order. Orient every face counterclockwise as seen from outside. A direct copy of
   T then shows its sides in the cyclic order (a, b, c) (a mirror copy would show (a, c, b)).
3. Around a vertex. Let v have degree d, edges e_1, …, e_d in counterclockwise order seen from
   outside, and face f_i between e_i and e_{i+1}. The boundary of f_i, counterclockwise, runs
   v → (along e_i) → … → (along e_{i+1}) → v, so e_{i+1} is the side that precedes e_i in the
   cyclic order of f_i: L(e_{i+1}) = σ⁻¹ L(e_i) with σ = (a b c). Going once around v gives
   σ^{−d} = 1, so 3 divides d, and the corners at v run through the types B, A, C, B, A, C, …
   (the corner between sides x and σ⁻¹x is opposite the third side). The angle sum at v is
   therefore (d/3)(A + B + C) = (d/3)π.
4. Convexity. A vertex of a convex polyhedron has angle sum < 2π, so d = 3 and the angle sum is
   π at every vertex. A triangulated sphere with all degrees 3 has 2E = 3V = 3F and
   V − E + F = 2, so V = 4: the polyhedron is a tetrahedron with corners A, B, C at each vertex,
   that is, opposite edges equal (a disphenoid). A disphenoid with faces T exists iff T is acute
   (for right T the four points are coplanar, for obtuse T none exist; standard, and also Lemma 5
   of arXiv:2608.01109).

Lean: [witness](B22.2/B22_2.lean).

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

### [C5.2](C5.2/): incomparable tilings cannot have all tiles close to squares

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section C5 (Tiling with incomparable rectangles and cuboids). Two rectangles are incomparable if
neither fits inside the other with sides parallel: with dimensions a1 x a2 and b1 x b2 suitably
labelled, a1 < b1 <= b2 < a2. Paraphrase of the question: for tilings of a rectangle with many
pairwise incomparable rectangles, can every tile have aspect ratio arbitrarily close to 1?

**Reading.** "Fit inside" allows rotation (the book's labelling with sorted sides). The answer
below holds also if rotation is not allowed (with constant sqrt 2 in place of 2).

**Result.** No. In every tiling of a rectangle by at least two pairwise incomparable rectangles,
some tile has aspect ratio (long side / short side) at least 2.

**Argument.** Write each tile with short side s and long side l, and let rho be the largest
aspect ratio. Suppose rho < 2.

1. *All sides lie in [m, rho m) for m the least short side.* Two tiles with equal short side are
   comparable, and if s_i < s_j then incomparability forces l_i > l_j. So the tile with the
   least short side m has the largest long side, which is at most rho m. Hence every side
   (width or height) of every tile lies in [m, rho m], and any side is less than twice any other
   side (rho m < 2m).
2. *Equal sides make tiles comparable.* If two tiles share a width (or a height, or a width of one
   equals a height of the other), the one with the shorter other side fits in the other.
3. *Two tiles share a side length.* Let A = [0,w] x [0,h] be the tile at the lower left corner of
   the tiled rectangle [0,W] x [0,H]. Since there are at least two tiles, w < W or h < H.
   - If w = W: the tiles meeting the segment y = h + (small), 0 < x < W, partition [0,W] into widths
     each at least m > W/2 (W = w <= rho m < 2m), so there is one such tile and its width is
     w. Symmetrically if h = H.
   - Otherwise let T be the tile just right of A's right side near its top corner (it contains
     points (w + d, h - d) for small d > 0), with vertical extent [y_b, y_t], y_b < h <= y_t.
     - If y_t = h: below T on the vertical line x = w + d lie tiles filling [0, y_b], each of
       height at least m. But y_b = h - height(T) <= rho m - m < m, so y_b = 0 and
       height(T) = h = height(A).
     - If y_t > h: T contains points (w + d, h + d). Let U be the tile just above A near A's
       right end (containing (w - d, h + d)). U and T have disjoint interiors, so U's right side
       is x = w. Its left side x_l = w - width(U) <= rho m - m < m, while the tiles left of U on
       the line y = h + d fill [0, x_l] with widths at least m; so x_l = 0 and width(U) = w =
       width(A).
   In every case two distinct tiles have a common side length, so by step 2 they are comparable,
   a contradiction.

Without rotation (incomparable meaning w_i < w_j forces h_i > h_j, and conversely), step 1 gives
(h_max / h_min)(w_max / w_min) <= rho^2, and step 3 needs only h_max < 2 h_min and
w_max < 2 w_min, so rho >= sqrt 2 for every such tiling.

The bound is about the existence question only; we did not determine the least possible maximum
aspect ratio (the 13 x 22 tiling of Yao, Reingold and Sands has a 1 x 18 tile).

Lean: —.

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

Lean: [checked](E4.4/E4_4_lrat.lean).

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

### [A12.2](A12.2/): Fickett's cosecant bound for congruent triangles is false

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section A12 (Overlapping convex bodies), after J. W. Fickett, Amer. Math. Monthly 87 (1980) 814-815.
For overlapping congruent convex sets K, K' with boundaries C, C', consider
L1/L2 = length(C ∩ K') / length(C' ∩ K). For congruent triangles with least angle psi the book asks
whether the maximum is cosec(psi/2) (the formula is garbled in our copy; the form
sin(psi/2) <= L1/L2 <= 1/sin(psi/2) is the one quoted by Rasskazova 2012 from the book and
Fickett).

**Result.** No. K = triangle (-5,0), (5,0), (0,12) (sides 10, 13, 13, least angle psi at the apex,
sin(psi/2) = 5/13, psi ≈ 45.24°) and K' = K rotated by (cos, sin) = (-5/13, -12/13) and translated by
(-3.1, 4.6) give L1 = 687563/26910 ≈ 25.551, L2 = 2363/414 ≈ 5.708, L1/L2 ≈ 4.476 > 13/5 = 1/sin(psi/2).
This agrees with N. V. Rasskazova (2012), who states that the bound fails for isosceles triangles
with apex angle psi in (2 arcsin(1/4), pi/3) and proves the sharp-looking bound
Q = 3 + 4 sin(psi/2) there (Q = 4.538 for psi here; our hill climbing reaches 4.532).

**Argument.** All coordinates are rational and all side directions have rational length, so the
part of each side inside the other triangle is a rational fraction of the side (clip the segment
against the three half-planes). Summing gives the exact values above.

Lean: [witness](A12.2/A12_2.lean).

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

### [A33.2](A33.2/): the Lamé oval |x|^2.001 + |y|^2.001 = 1 has five-point hyperbolas

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991),
Section A33 (conics through five points). Paraphrase: Reznick asks what can be said about an
infinite set S, for instance a union of rectifiable curves, if every five-point subset of S
determines an ellipse (or, respectively, a hyperbola). The book adds the suggestion that
|x|^2.001 + |y|^2.001 = 1 yields only ellipses.

**Reading.** Two parts: the open-ended "describe such sets", and the specific suggestion about
the oval. Only the specific suggestion is settled here.

**Result.** The suggestion is false. Take p = 2001/1000 and the five points on the oval with
y_k = k/1000 and x_k = (1 − y_k^p)^{1/p}, k = 1..5 (all near the vertex (1,0), on one side of
it). Their conic a x² + b xy + c y² + d x + e y + f = 0 is a nondegenerate hyperbola, with
b² − 4ac ≈ 5.169·10^{−56} > 0. The same holds for y_k = k/10^4 and k/10^5. The scales
k/10 and k/100 give ellipses.

**Argument.** Near (1,0) the oval is u ≈ y^p/p with u = 1 − x. Georgiou (below) proves that
any five points on a power curve u = a y^p with p > 2 and y > 0 determine a hyperbola. As the
five points shrink toward the vertex, the oval's own five-point conic converges to that case.
The certificate does not use this limit argument. It computes the conic coefficients as signed
5×5 minors (Cramer's rule) in 120-digit interval arithmetic. The interval for b² − 4ac is
strictly positive, and the interval for the 3×3 conic determinant excludes 0.

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

### [C1.3](C1.3/): repeated subdivision of tetrahedra with a(T)/r(T) bounded (Hajós)

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991), C1 (end of section), citing G. Hajós, Problem 122, Colloq. Math. 3 (1954) 74. Paraphrase: with a(T) the longest edge and r(T) the inradius of a tetrahedron T, give an effective way to decompose any T into finitely many tetrahedra, then each of those, and so on, so that a/r stays bounded over all generations.

**Reading.** The pieces are meant to shrink (otherwise "do not subdivide" works); the construction below halves the diameter at every generation.

**Result.** Yes; answered by Freudenthal in 1942 (for simplices of every dimension, as an answer to a question of Brouwer).

**Argument.** Write T = A(S) with A affine and S = {1 ≥ x1 ≥ x2 ≥ x3 ≥ 0} (Kuhn simplex). Generation k cuts S by the hyperplanes x_i = m/2^k and x_i − x_j = m/2^k (m integer). All facet hyperplanes of S belong to this arrangement, and inside each cube of side 2^−k the arrangement gives the 3! = 6 Kuhn simplices S_π (π a permutation) scaled by 2^−k. So S is a union of 2^(3k) translates of the S_π/2^k, generation k+1 refines generation k, and the pieces of T are translates of A(S_π)/2^k. a/r is invariant under translation and scaling, so over all generations it takes at most 6 values (Freudenthal; Bey shows 3 congruence classes suffice for tetrahedra with a suitable vertex order). The construction is explicit.

Lean: —.

### [C3.1](C3.1/): Mrs Perkins's quilt, f(n) beyond 100 and Selfridge's prime sets

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section C3. f(n) is the least number of squares in a prime (gcd 1) dissection of an n × n square
along lattice lines; values were known "with some slightly increasing lack of confidence" for
n ≤ 100. Selfridge noted (from the Brooks–Smith–Stone–Tutte finiteness theorem) that for each N all
but finitely many primes p have p × p squares that cannot be dissected into N squares, and the book
asks for this set of primes for each N.

**Reading.** For prime p and N ≥ 2, a dissection of p × p into N squares is automatically prime.
So the set asked for is {p prime : T(p, N) = 0}, where T(n, N) counts prime dissections of an n × n
square into N squares. Since T(n, N) > 0 forces f(n) ≤ N, only finitely many p need checking.

**Result.** Answered computationally elsewhere for the computable range.
- f(n) is now known exactly for n ≤ 120 (E. Wynn, b-file of OEIS A005670, 2013), with the n ≤ 100
  values confirmed.
- E. Wynn, *Exhaustive generation of Mrs Perkins's quilt square dissections for low orders*,
  Discrete Math. 334 (2014) 38–47, arXiv:1308.5420, generated all prime dissections of order
  N ≤ 18 (plantri on triangulations, cross-checked by a direct method). Its Table 1 gives T(n, N)
  for every n and N ≤ 18, and its Table 3 gives the largest size g(N) (OEIS A089047). This settles
  Selfridge's set for every N ≤ 18: the primes p ≤ g(N) with T(p, N) = 0, together with all primes
  p > g(N).
The question "for each N" (all N) is a request for an infinite table and has no closed answer.

Lean: —.

### [C10.2](C10.2/): the plane can be tiled with exactly one square of each positive rational side

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991),
Section C10 (squares tiling the plane). Question: can the plane be tiled using exactly one
square of each positive rational side?

**Result.** Yes. F. V. Henle and J. M. Henle, *Squaring the plane*, Amer. Math. Monthly 115
(2008) 3–12, tile the plane with one square of each positive integer side (Golomb's
heterogeneous tiling conjecture). The authors note that their algorithm can easily be used to
tile the plane with one square of every rational side (squaring.net, *Squaring the Plane I*,
quoting the Henles).

**Argument (re-derived).** The Henle construction alternates two steps.
1. *Fill.* Place the next unused size at a fixed corner of the current tiled region. For
   integers this is the smallest unused size. For the rationals, fix an enumeration
   q_1, q_2, … of Q_{>0} and use the first unused q_i.
2. *Puff up.* Extend the current region (an L-shape) to a perfect tiled rectangle. The new
   squares have sizes that are integer combinations of sizes already placed, each larger than
   every size used so far.

Step 2 stays valid over Q. Integer combinations of rationals are rational. Only finitely many
sizes are in use at any stage, so sizes above the current maximum are unused, and the sizes in
one puff-up step are distinct because they increase strictly. Step 1 uses every q_i
eventually, because after the i-th fill step q_1..q_i are all placed. The plane-covering part
of the Henle proof (the rectangles grow in all four directions in turn) does not depend on
which size step 1 inserts. So every positive rational appears exactly once and the union is
the plane.

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

### [C16.3](C16.3/): settled order by order up to n = 25; no general rule

**Source.** Croft-Falconer-Guy, Unsolved Problems in Geometry (1991), C16 Polyominoes
(paraphrased): decide which n-ominoes tile the plane for n >= 9.

**Reading.** Tiling by congruent copies (rotations and reflections allowed), polyominoes in
Myers' convention (holes allowed; holed ones never tile). "Determine" read as either a
per-order classification or a general criterion.

**Result.** Partial, known. Per order the question is answered by exhaustive computation:
J. Myers, Polyform tiling (polyomino.org.uk, computations 1996-2003, extended to higher orders
by Paul Church), with counts in OEIS A054359 (n-ominoes that tile, b-file n = 1..25, for
example 1050 9-ominoes and 271293803 25-ominoes tile) and A054360 (n-ominoes that do not tile,
b-file to n = 25), and A075198 (tiling by translation). These are unrefereed computations.
No criterion for all n is known; whether tiling the plane by one polyomino (isometries
allowed) is algorithmically decidable is open, while tiling by translations alone is decidable
(Beauquier-Nivat boundary-word criterion, 1991). So the problem as a whole stays open.

**Argument.** Citation only.

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

### [F13.2](F13.2/): n non-collinear points determine at least n-2 angles, proved for large n

**Source.** Croft-Falconer-Guy, Unsolved Problems in Geometry (1991), F13 (paraphrased): do n
points, not all on a line, determine at least n-2 distinct angles? Same question:
Brass-Moser-Pach, Research Problems in Discrete Geometry (2005), Section 6.2, Conjecture 10
(Corradi-Erdos-Hajnal), angles counted in [0, pi). The regular n-gon shows n-2 is best possible.

**Result.** Partial, known. K. Bhowmick, O. Roche-Newton, A. Warren, Point sets determining
few angles are almost contained in a line or circle, arXiv:2609.15270 (2026), Theorem 2: for n
sufficiently large every non-collinear n-point set in R^2 determines at least n-2 angles, and
the regular n-gon is the unique minimiser. The threshold n0 is not explicit (it comes from a
structure theorem with an absolute constant c > 0 and incidence bounds), so the claim for small
and moderate n stays open; it is not a finite check because the configurations are continuous.

**Argument.** Citation only. Their Theorem 1: unless P is (almost) on a line or a circle in one
of four listed ways, some point of P sees at least n^{1+c} angles; the exceptional forms are
then checked by hand to give at least n-2 angles.

Lean: —.

### [A4.4](A4.4/): billiards in the regular tetrahedron — every periodic orbit has even period

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991), section A4
(paraphrased): Steinhaus asked whether every polyhedron has a periodic billiard orbit. Conway showed circuits
exist in all tetrahedra and said the regular tetrahedron has a continuous family of periodic quadrangles, two
periodic hexagons, and no other orbits with fewer than eight bounces. Are there periodic orbits with arbitrarily
many bounces, and do they all have an even number of bounces?

**Reading.** Billiard trajectories avoid edges and vertices; a periodic orbit returns to its starting point with
its starting direction after k bounces (k minimal).

**Result.** Partial.
1. (New, proved.) In the regular tetrahedron every periodic billiard orbit has an even number of bounces.
2. (New, proved.) Every periodic orbit is isolated: there is no continuous (parallel) family of periodic orbits
   of any period. This contradicts the "continuous family of periodic quadrangles" as reported in the book;
   there are exactly three periodic quadrangles (each hitting the four faces once, one per cyclic order up to
   reversal).
3. (Computation, exact.) Primitive periodic orbits exist with k = 4, 6, 12, 14, 16, 18, 20 bounces and none with
   k = 2, 8, 10 (exhaustive for k ≤ 10 by the exact search; for 12 ≤ k ≤ 20 a floating-point screen whose hits
   were all verified exactly). Numbers of primitive cyclic face words (rotations of words starting with face 0):
   k = 4: 6, 6: 20, 12: 80, 14: 36, 16: 12, 18: 16, 20: 72. This supports "arbitrarily many bounces"
   but does not prove it. Steinhaus's question for all polyhedra stays open.

**Argument.** Faces: n_f · x = 1 with n_f = −V_f, V_f the vertices (±1,±1,±1) with an even number of minus
signs. The reflection in face f is x ↦ L_f x + t_f with 3L_f = 3I − 2 n_f n_fᵀ. A periodic orbit with cyclic face
word w = f_1 … f_k unfolds to a line ℓ with G(ℓ) = ℓ, G = σ_{f_1} ∘ … ∘ σ_{f_k}, preserving the direction u, so
L_w u = u for the linear part L_w = L_{f_1}⋯L_{f_k}.
- Mod 3: 3L_f ≡ n_f n_fᵀ, and n_f · n_g = −1 for f ≠ g, so 3^k L_w ≡ (−1)^{k−1} n_{f_1} n_{f_k}ᵀ (mod 3) and
  trace(3^k L_w) ≡ (−1)^k (mod 3) when f_k ≠ f_1. Hence trace(L_w) ≠ 1 and L_w ≠ I (both give a trace of
  3^k L_w divisible by 3).
- Odd k: L_w is orthogonal with det −1 and eigenvalue 1, so its eigenvalues are 1, 1, −1 and its trace is 1;
  impossible. So k is even.
- Even k: L_w is a rotation ≠ I fixing u, so G is a screw motion whose only invariant line parallel to u is its
  axis. Hence the orbit with word w is unique, i.e. isolated, and orbits are found by testing the axis of G_w.

Lean: [full proof](A4.4/A4_4.lean).

### [C8.2](C8.2/): more than 120 congruent "non-thin" triangles on the sphere?

**Source.** Croft, Falconer, Guy, *Unsolved Problems in Geometry* (1991), §C8 (dissecting the sphere
into small congruent pieces), paraphrased: the spherical icosidodecahedron gives a nontrivial dissection of the
sphere into 120 congruent triangles; can this number be increased without the triangles becoming "too thin",
the book suggesting a bound on the side lengths (the bound is illegible in our scan, "less than in", most likely
π/2); Sommerville and Davies treated the case where no vertex lies inside an edge of another triangle.

**Reading.** "Tiling" = covering the sphere by congruent copies (reflections allowed) with disjoint interiors.
Edge-to-edge = no vertex of a tile in the interior of an edge of another (the Sommerville-Davies setting).
"Not too thin" is not defined in the book; we treat (i) the side bound π/2, (ii) a side bound b ≤ π/3, and
(iii) a lower bound on the angles.

**Result (partial).**
1. With the side bound π/2 the answer is yes, and trivially so: the edge-to-edge tilings with F = 4n tiles by the
   isosceles triangle with angles ((n−1)π/2n, (n−1)π/2n, 2π/n) (n ≥ 4) and with F = 8n tiles by its half, the
   right triangle (π/2, (n−1)π/2n, π/n), have all sides < π/2 (longest side decreasing to π/3). Their smallest
   angle tends to 0, so the side bound π/2 does not prevent thin tiles.
2. Edge-to-edge, with all sides < b for a bound 37.38° < b ≤ 60°: the maximum number of tiles is exactly 120
   (attained by the (π/2, π/3, π/5) triangle, sides 20.91°, 31.72°, 37.38°).
3. Edge-to-edge, more than 120 tiles forces a smallest angle ≤ 8π/F < π/15.
4. Non-edge-to-edge tilings: open here. Their classification is complete only for triangles with an irrational
   angle (Chen, Liang, Wang 2025) and for right and isosceles triangles (Dawson; Dawson and Doyle); the all-rational
   case is not finished.

**Argument.** Ueno and Agaoka (2002, Theorem 1 and Corollary 3) classify all edge-to-edge monohedral triangle
tilings of the sphere. The triangles that tile are: the F = 4 family (angle sum 2π), five rigid sporadic
triangles with F = 24, 48, 60, 60, 120, and four infinite families: (π/2, π/2, 2π/n) with F = 2n (two sides
π/2); ((n−1)π/2n, (n−1)π/2n, 2π/n) with F = 4n (legs a with cos a = (1 − tan²(π/2n))/2 < 1/2, so π/3 < a < π/2,
base < π/2 for n ≥ 4); (π/2, (n−1)π/2n, π/n) with F = 8n (its hypotenuse is a leg of the previous triangle,
> π/3); and α + β = π, γ = π/n with F = 4n (then the opposite sides satisfy a + b = π, so one side ≥ π/2).
F = 4 triangles have area π and a side > π/3 (a triangle with sides ≤ π/3 lies in the cap of radius π/3 about a vertex, of area π, and is a proper part of it). So every tiling with F > 120 uses a triangle from an infinite
family, with a side > π/3 and smallest angle ≤ 2π/n ≤ 8π/F, and the sporadic maximum is F = 120. Item 1 is the
F = 4n and F = 8n families with the side computations above.

Lean: —.

### [F9.1](F9.1/): nine points with 19 unit circles through three of them, so f(9) ≥ 19

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section F9. f(n) is the largest number of unit circles each passing through at least 3 points of an
n-point plane set. Known: f(3), ..., f(8) = 1, 4, 4, 8, 12, 16 (Harborth–Mengersen 1986; OEIS
A003829). The value f(9) is asked for.

**Result.** f(9) ≥ 19 (previous lower bound 16 = f(8)). Upper bound n(n−1)/3 = 24 (Harborth–Mengersen).
f(9) itself stays open.

**Argument.** Exact arithmetic in Q(√3, √11): each listed centre has squared distance 1 to three
listed points, the centres are distinct, so the 19 unit circles are distinct.

Lean: [witness](F9.1/F9_1.lean).

### [F15.2](F15.2/): worst-case shortest path through 4 points of the unit square is 3

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

Lean: —.

### [F17.3](F17.3/): maximum-volume polyhedron with 10 vertices on the unit sphere

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer
1991, section F17 (arranging points on a sphere): find the polyhedron of largest volume whose
vertices are N points of the unit sphere. Solved for N ≤ 8 (Berman–Hanes 1970), N = 12
(icosahedron) and N = 9 (Hoehner–Ledford, arXiv:2608.04392, 2026). N = 10 is open; Hoehner and
Ledford say it will be treated in a forthcoming paper by Hoehner.

**Result (partial; the problem stays open).**

1. *Candidate in closed form.* The best configuration found (300 random starts, every run
   converging to it or to something worse) is a bicapped square antiprism: poles (0, 0, ±1)
   and two squares at heights ±h rotated by 45°. Its volume is
   V(h) = 4/3 + (4/3)(1 + √2) h − (4/3) h² − (4/3)(1 + √2) h³, maximised at the root of
   3(1 + √2) h² + 2h − (1 + √2) = 0, h* = 0.455559157…, with
   V* = (48 + 16√2 + (48√2 − 32)√(5 + 3√2)) / 81 = 2.21871113154539940…
   This matches the best known value 2.21871 in the Hardin–Sloane–Smith tables.
2. *No trivalent vertex for 10 ≤ N ≤ 21.* Hoehner–Ledford's Lemma 3.10 (valid for every
   N ≥ 5) bounds the volume of any simplicial polytope inscribed in S² with o in its interior
   and a vertex of degree 3 by an explicit function F_N(α) of one angle α ∈ [0, 4π].
   Interval arithmetic gives max F_N below a certified volume of an explicit N-point
   configuration for every N in {10, 11, 13, …, 21} (N = 12 is the icosahedron, already
   solved). With their Lemma 3.3 (a maximiser contains o in its interior) and Berman–Hanes
   (a maximiser is simplicial), a volume maximiser for these N has no vertex of degree 3.
   Margins: N = 10: max F ≤ 2.18960 < 2.21871; the smallest margin is at N = 21
   (3.16135 < 3.16444). For N = 22 the bound no longer beats the configurations found.
3. *Reduction for N = 10.* Simplicial 10-vertex polytopes with minimum degree ≥ 4 are exactly
   the 12 triangulations of the sphere with 10 vertices and minimum degree 4 (plantri -m4 10;
   all 233 triangulations without the degree condition). So the N = 10 problem is reduced to
   maximising the volume over 12 combinatorial types, one of which (degree sequence
   4,4,5,…,5) holds the candidate of item 1. The other local maxima found are 2.20091
   (degrees 4,4,4,5⁶,6), 2.15509, 2.08261 and lower.

| N | 10 | 11 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| upper bound of max F_N | 2.18960 | 2.34445 | 2.59453 | 2.69653 | 2.78658 | 2.86660 | 2.93813 | 3.00243 | 3.06053 | 3.11327 | 3.16135 |
| certified volume found | 2.21871 | 2.35463 | 2.61283 | 2.72098 | 2.80438 | 2.88646 | 2.94752 | 3.00961 | 3.06322 | 3.11854 | 3.16444 |

**Argument.** Item 1: sum of the 16 facial tetrahedra with apex o (`certificate/bsa.py`,
exact symbolic computation; the derivative's numerator is −4(3(1+√2)h² + 2h − (1+√2))).
Item 2: F_N is evaluated in mpmath interval arithmetic on 20 000 subintervals of [0, 4π]; the
maximum of the upper endpoints is the bound (`certificate/triv.py`). The lower bounds come from
numerical configurations (`certificate/best_N.json`) whose coordinates are rounded to rationals
and scaled into the closed unit ball; the hull volume is then computed exactly with rational
arithmetic after checking every facet plane exactly (`certificate/certify_lb.py`). A point set
inside the ball gives a lower bound for the sphere problem, because the hull volume is a convex
function of each vertex, so pushing vertices radially to the sphere cannot lower the maximum.
Item 3: plantri enumeration (`certificate/types10.txt`, the 12 types in plantri ASCII
format); every triangulation of the sphere is the boundary of a simplicial convex polytope
(Steinitz).

Lean: —.

### [G9.2](G9.2/): two sets always meeting in exactly n points — odd n is impossible for curve-like sets

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991), section G9
(paraphrased): Steinhaus asked for two plane sets that meet in exactly one point however they are placed
(Sierpiński: yes, using the axiom of choice). For sets always meeting in exactly n points, n even has a simple
example: parallel lines at unit spacing and a circle of radius n/4. Are there such simple examples for odd n?

**Reading.** "Placed" = moved by a rigid motion g (orientation-preserving; the result also holds with
reflections). N(g) = |A ∩ gB|. "Simple" is read as: both sets are curve-like (locally finite embedded graphs).

**Result.** Partial (negative for the natural class). Let A be a locally finite union of straight lines and B a
compact embedded graph with finitely many C¹ edges. If N(g) = n for every rigid motion g, then n is even.
So the even-n example (lines and a circle, or lines and any closed curve of constant width n/2) has no odd-n
analogue with A a family of lines and B a finite union of arcs; odd n needs a set that is not a finite union
of arcs. The same argument (sketched below) applies when A is any locally finite embedded C² graph.
An explicit odd-n example (simple or Borel) remains open.

**Argument.** (1) Every vertex of B has even degree. Suppose p is a vertex of odd degree (an endpoint has degree
1). Choose g₀ with g₀(p) on a line λ of A, all edges of g₀B at g₀(p) transverse to λ, and no other vertex of g₀B
on A. Moving g across the wall W_p = {g : g(p) ∈ A} changes the number of intersections near g(p) by
deg(p) − 2k for some k, an odd number. Tangencies elsewhere change N by 0 or ±2. Another vertex p′ can lie on A
for all g in an open subset of W_p only if A contains, for each a in an interval of λ, an arc of the circle of
radius |p − p′| around a, i.e. a set with interior; A has none. So such g₀ exist, N mod 2 changes across W_p,
and N is not constant. (2) With all degrees even, B is a mod-2 1-cycle; being compact in ℝ² it bounds a compact
2-chain D (mod 2). For g with gB transverse to every line of A (generic g), each line λ meets gB = ∂(gD) in an
even number of points (λ ∩ gD is a finite union of segments whose endpoints are exactly λ ∩ gB). Summing over
the finitely many lines meeting gB, N(g) is even. Since N is constant, n is even.
General A (sketch): the wall argument works for vertices of A as well (use g⁻¹), with the extra case of an edge
of A that is a circle arc centred at a vertex of A, which one avoids by choosing the crossing point on another
edge; step (2) uses that a locally finite even-degree graph meets a compact mod-2 boundary evenly.

Lean: —.

