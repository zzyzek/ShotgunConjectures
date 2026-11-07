# CFG E4: Birch's 8-point question holds for points in general position

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section E4. Birch asks whether every set of 8 points in the plane can be
partitioned into two triangles and a segment so that the segment cuts the interior of both
triangles.

**Reading.** "Triangle" = convex hull of three of the points; "cuts the interior" = the segment
meets the open triangle.

**Result.**
- Points in general position (no three collinear): yes.
- As literally stated, for arbitrary sets: no. With 7 collinear points and one more, a triangle
  with nonempty interior must use the off-line point, so two such triangles cannot coexist.

**Argument.** For points in general position the property depends only on the orientations of
triples. Sort the points by x-coordinate (after a rotation). The orientations form a signotope
(for i < j < k < l the sequence χ(ijk), χ(ijl), χ(ikl), χ(jkl) changes sign at most once), so a
SAT encoding over all signotopes covers every general-position set (and possibly non-realizable
ones, which only strengthens UNSAT). "Segment pq meets open triangle abc" is exact in general
position as: p or q strictly inside, or pq properly crossing an edge. Forbidding all 280
partitions is UNSAT.

**Evidence.** Second reader, independent encoding (written without reading the scan's `om.py`):
- `certificate/e44_sat.py`: 616 variables, 9800 clauses (scan: 3104/37240, different Tseitin
  form); UNSAT with CaDiCaL 1.5.3 (PySAT). Controls: the encoding counts 62 and 908 signotopes
  on 5 and 6 points (known values); weakening "meets" to "an endpoint is inside" makes the
  8-point instance SAT, as it must.
- The UNSAT proof (`e44.drat.gz`, 1586 lines, with the CNF `e44.cnf.gz`) was checked by
  `certificate/rupcheck.py`, a small forward RUP checker written for this review: all 750 added
  lemmas are RUP and the empty clause is derived. drat-trim was not available.
- `certificate/e44_geom.py`: on 2000 random integer 8-point sets in general position, the
  orientation assignment satisfies the signotope clauses, the clause-level "meets" predicate
  agrees with an exact rational segment/open-triangle test in every case, and every set has a
  Birch partition.
- The scan's `om.py`, `controls.py`, `birch8.py` are copied.
- Lean, SAT part: [`E4_4_lrat.lean`](E4_4_lrat.lean), theorem `birch_cnf_unsat : Unsat birchCnf`, where
  `birchCnf` is the clause list of `certificate/e44.cnf` (read at elaboration time). Checked with the
  library LRAT checker `OpenProblemsLib.LRAT` (guide `lib/docs/lrat.md`) on the CaDiCaL 2.1.3 proof
  [`certificate/e44.lrat`](certificate/e44.lrat) (625 additions, 7890 hints): 20 s, 2.0 GB. Axioms propext,
  Classical.choice, Quot.sound (2026-11-07).
  Outside Lean: that the CNF encodes the geometry, i.e. (1) `certificate/e44_sat.py` writes the signotope
  axioms, the Tseitin clauses for "segment meets open triangle" and one clause per partition as described
  above, and (2) every 8-point set in general position, sorted by x, gives a signotope whose orientations
  satisfy it, with "segment pq meets the open triangle abc" equivalent to "p or q strictly inside, or pq
  properly crosses an edge" (a real-geometry argument with no Mathlib support yet).
Not done: cross-check against the 3315 order types of 8 points (Aichholzer's database needs a
download).

**Review level.** `rechecked` (the SAT part is kernel-checked in Lean; the geometric reduction is not).
**Prior art.** No resolution found. Searched: web (standard and extended) on Birch's 8-point question, [Hell, arXiv math/0612823](https://arxiv.org/abs/math/0612823) (Birch partitions; not this question), the Tverberg survey [Bárány–Soberón, arXiv 1712.06119](https://arxiv.org/abs/1712.06119). Brass–Moser–Pach (2005) was not accessible. Verdict: new. 2026-11-04.
