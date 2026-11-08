# Croft–Falconer–Guy F17: maximum-volume polyhedron with 10 vertices on the unit sphere

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

**Evidence.** Scripts and data in `certificate/`. No Lean: the inputs are real-analytic bounds
(Hoehner–Ledford's lemmas, interval evaluation of tan). Outside Lean: everything, namely the
Hoehner–Ledford Lemmas 3.3 and 3.10 and Berman–Hanes simpliciality (cited, not re-proved), the
interval computation of max F_N, the exact rational volume computations, and the plantri count.

**Review level.** agent (items 2 and 3 re-derived from the published lemma statement; Lemma
3.10 itself not re-proved here). Checked: the N = 9 instance of the same computation gives max
F_9 ≤ 2.00901 < 3√(2√3 − 3) = 2.04375, consistent with Hoehner–Ledford's stated F_9 < 2.037.

**Prior art (2026-11-07).** Hoehner–Ledford 2026 (arXiv:2608.04392) prove Lemma 3.10 for all
N and use it only for N = 9; they announce N = 10 as forthcoming. Best known volumes:
Hardin, Sloane, Smith, tables of maximal-volume arrangements of points on the sphere. The
closed form of item 1 was not found in the sources checked. google-deepmind/formal-conjectures
has no entry for this problem.
