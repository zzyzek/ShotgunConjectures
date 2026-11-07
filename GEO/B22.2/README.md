# GEO B22.2: no convex polyhedron has all faces directly congruent to a right or obtuse scalene triangle

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

**Evidence.** Lean (core): [`B22_2.lean`](B22_2.lean). `rec_closed`, `label_cycle_rec` (labels
with L(i+1) = L(i) + 2 mod 3 that close up after d steps force 3 ∣ d), `all_degree_three`
(V = 4 from the Euler relations), `one_triple`. Axioms: propext, Quot.sound. Checked with
tools/leancheck.sh, no warnings. Outside Lean: the geometric steps 1, 2, 3 (orientation), the
convexity bound on vertex angle sums, and the disphenoid fact.

**Review level.** `lean-witness` (finite combinatorial core in Lean; geometry by hand).

**Prior art.** Searched 2026-11-07: *Congruent triangular faces, reflections allowed:
universal realization and the minimum face count in Problem B22*, arXiv:2608.01109 (2026), which
states that the orientation-preserving case is open only for right and obtuse scalene triangles and
that its 8-face construction uses mirror copies; web search (disphenoid literature, "directly
congruent faces"); google-deepmind/formal-conjectures (no entry). The argument is short, so it may
be folklore, but no statement of it was found.
