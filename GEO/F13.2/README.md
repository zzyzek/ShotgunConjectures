# UPIG F13 / BMP 6.2 Conj. 10: n non-collinear points determine at least n-2 angles, proved for large n

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

**Evidence.** arXiv:2609.15270 abstract and statements of Theorems 1, 2, 6, read 2026-11-06.
No Lean. Outside Lean: everything.

**Review level.** `agent`.

**Prior art.** Searched 2026-11-06: arXiv 2609.15270 (full text grep for an explicit n0: none),
google-deepmind/formal-conjectures HEAD 2026-11-06 (no distinct-angles entry).
Pointer: [BMP 6.2.10](../../BMP/6.2.10/README.md) is the same problem.
