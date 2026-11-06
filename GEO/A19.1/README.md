# CFG A19 (first question): minimal perimeter of a plane convex set of given diameter and width

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

**Evidence.** README only. Lean: none. Mathlib has no Cauchy perimeter formula or width function for
convex bodies, and a formal proof would be a project in itself. Outside Lean: Cauchy's formula and
the argument above (re-derived for this write-up).

**Review level.** `rechecked`: the bound and the equality case were re-derived (above); they agree
with the published row.

**Prior art.** Verdict `known` (immediate). Sources:
P. R. Scott, P. W. Awyong, Inequalities for convex sets, JIPAM 1(1) (2000) Art. 6, Table 3.1 row 13
(d, p, w): p >= 2 sqrt(d^2 - w^2) + 2 w arcsin(w/d), sharp for the hull of a disk and two
symmetric points; credited to I. M. Yaglom and V. G. Boltyanskii, *Convex Figures*, exercise 7.18(b).
L. Santaló, Math. Notae 17 (1961) 82-104, via M. A. Hernández Cifre, G. Salinas, S. Segura Gomis,
JIPAM 2(1) (2001) Art. 10: the (p, d, w) system of inequalities is complete. Both citations are from
the scan's tier-3 literature pass; the JIPAM mirror at emis.univie.ac.at did not respond on
2026-11-05, so the table row was not re-read for this write-up. Searched: the CFG text,
google-deepmind/formal-conjectures (tree listing: no CFG A19 file), 2026-11-05.
