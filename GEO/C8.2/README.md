# GEO-C8.2: more than 120 congruent "non-thin" triangles on the sphere?

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

**Evidence.** [`certificate/sides.py`](certificate/sides.py): side lengths (spherical law of cosines for angles) of
the sporadic triangles and of the infinite families for n ≤ 399: in the F = 4n and F = 8n families all sides are
< 90° and the longest side stays > 60°; the (π/2, π/3, π/5) triangle has sides 20.91°, 31.72°, 37.38°.
Lean: none. Outside Lean: everything (the classification is cited, not re-derived).

**Review level.** `agent` (the edge-to-edge classification is cited; side computations rechecked numerically).

**Prior art** (2026-11-06). Y. Ueno, Y. Agaoka, Classification of tilings of the 2-dimensional sphere by congruent
triangles, Hiroshima Math. J. 32 (2002) 463-540; R. J. MacG. Dawson, Tilings of the sphere with isosceles
triangles (2003) and with B. Doyle, Tilings of the sphere with right triangles I-III, Electron. J. Combin. 13-14
(2006-2007); H. M. Cheung, H. P. Luk, M. Yan, arXiv:2204.02736 (modern edge-to-edge classification);
Chen, Liang, Wang, Non-side-to-side tilings of the sphere by congruent triangles with any irrational angle,
arXiv:2505.16629 (2025), which states that the non-side-to-side classification is still incomplete.
