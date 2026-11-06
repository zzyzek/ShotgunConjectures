# OEIS A177390 / A132870: Hanna's "integer triangle for every k" fails at k = 1 (and k = 3)

**Source.** [A177390](https://oeis.org/A177390) (Paul D. Hanna, May 25 2010): "Triangle T where the
g.f. of row n of T^(2n) = (2n^2 + y)^n". Comment: "Conjecture: for all integer k, there exists an
integer triangle J such that the g.f. of row n of J^(k*n) = (k*n^2 + y)^n for n>=0." The k = 1
triangle is [A132870](https://oeis.org/A132870), which carries the same conjecture in the scan list
(OEIS wiki Talk:Conjectures/List). OEIS text CC BY-SA 4.0, checked 2026-11-06.

**Reading.** "Triangle" as in both entries and in the Pascal analogy: lower triangular with 1 on the
diagonal. Then row n of J^(kn) is a polynomial identity whose coefficient of y^j involves J(n,j)
with factor kn (all diagonal entries 1), so for k != 0 the rows are determined one after another
and the rational solution is unique. If the diagonal is not required to be 1, the question changes:
J(0,0) is unconstrained, and J(0,0) = 0 makes column 0 integral automatically (its coefficient
becomes 1); that looser reading is not settled here.

**Result.** False (unitriangular reading). For k = 1 the unique rational solution (A132870) has
T(30,0) = R/2 with R odd; so no integer triangle exists for k = 1. The same happens for k = 3
(row 30, column 0). For k = 2 (A177390 itself) all entries are integers through row 36.
Known: A132870 states since Nov 19 2017 (M. F. Hasler, noticed by Alois P. Heinz) that from row 30
on the entries are not integers, and its name was restricted to 0 <= n <= 29. A177390's conjecture
was not updated.

**Argument.** Uniqueness: write J's row n as unknowns. In J^e (e = kn), entry (n, j) equals
e * J(n,j) plus terms in rows < n and in J(n,l) for l > j (a product path from n to j leaves row n
exactly once; if it leaves straight to column j, the other e - 1 factors are diagonal 1s). So
solving from j = n-1 down to 0 determines row n. Computing rows 0..30 for k = 1 gives integers for
rows 0..29 and T(30,0) = R(0)/2 with R(0) odd.

**Evidence.**
- Lean (core): [`A177390.lean`](A177390.lean). Main theorem `A132870_row30_not_integral`: the
  integer rows 0..29 satisfy "row n of rows^n = coefficients of (n^2 + y)^n" for every n < 30
  (`eq_upto29`, one `decide +kernel` per row), the row R/2 completes row 30 (`eq_row30`, checked
  as 2 * row 30 of T^30 = 2 * target), and R(0) is odd (`R0_odd`). Axioms propext, Quot.sound.
- [`certificate/solve2.py`](certificate/solve2.py) (exact fractions; log in `solve2.log`):
  k = 1 and k = 3 fail first at (30, 0); k = 2 integral through row 36.
  [`certificate/genlean.py`](certificate/genlean.py) writes the data part of the Lean file.
- Outside Lean: the uniqueness step above (that an integer solution would have to equal the
  computed one).

**Review level.** `lean-witness`.

**Prior art.** Known: A132870 (comment and name change by M. F. Hasler, Nov 19 2017; b-file stops
at row 29). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (grep
A177390, A132870, 2026-11-06).
