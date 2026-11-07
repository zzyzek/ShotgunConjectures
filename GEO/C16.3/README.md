# UPIG C16 (n-ominoes that tile the plane, n >= 9): settled order by order up to n = 25; no general rule

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

**Evidence.** OEIS A054359, A054360 b-files and Myers' page, read 2026-11-06. No Lean.
Outside Lean: everything.

**Review level.** `agent`.

**Prior art.** Searched 2026-11-06: OEIS (polyominoes tile plane), Myers' polyform-tiling page,
google-deepmind/formal-conjectures HEAD 2026-11-06 (no polyomino-tiling entry).
