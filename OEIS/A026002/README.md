# OEIS A026002: Bergot's array with borders n(n−1)+1 has diagonal A026002

**Source.** [A026002](https://oeis.org/A026002) (offset 1), Clark Kimberling: "a(n) = T(n,n+2), where T = Delannoy
triangle (A008288)", data 1, 7, 41, 231, 1289, ... Comment by J. M. Bergot (Apr 24 2013): "Conjecture: define an
infinite array to have m(n,1) = m(1,n) = n*(n-1)+1 in the first row and column, and
m(i,j) = m(i,j-1) + m(i-1,j-1) + m(i-1,j); then m(n,n) = a(n)." (OEIS text, CC BY-SA 4.0, revision #77 of
Sep 22 2025, checked 2026-11-06.)

**Reading.** D(i, j) (i, j ≥ 0) is the square Delannoy array of A008288: D(i,0) = D(0,j) = 1,
D(i,j) = D(i−1,j) + D(i−1,j−1) + D(i,j−1). With offset 1 the data are a(n) = D(n−1, n+1) (D(0,2) = 1, D(1,3) = 7,
D(2,4) = 41; Deutsch's formula a(n) = (1/n) Σ_k k C(n,k) C(n+k,k+1) agrees). The recurrence in the conjecture
applies for i, j ≥ 2.

**Result.** True, with the closed form 2·m(i,j) = D(i−1, j+1) + D(i+1, j−1) for all i, j ≥ 1. On the diagonal the
two terms are equal (D is symmetric), so m(n,n) = D(n−1, n+1) = a(n).

**Argument.** Both F(i,j) = D(i−1, j+1) and G(i,j) = D(i+1, j−1) satisfy the recurrence at every i, j ≥ 2 (all
indices stay in the range where the Delannoy recurrence holds). On the border j = 1: D(i−1, 2) = 2(i−1)² + 2(i−1) + 1
= 2i² − 2i + 1 and D(i+1, 0) = 1, sum 2(i(i−1) + 1); the border i = 1 is symmetric. So F + G and 2m agree on the
borders and satisfy the same recurrence, hence agree everywhere (induction on i, then j).

**Evidence.**
- Lean (Mathlib): [`A026002_mathlib.lean`](A026002_mathlib.lean). Definitions `D`, `A026002 n = D (n−1) (n+1)`,
  `M`/`bergot` (the array, built by recursion). Theorems: `D_symm`, `D_one` (D(1,j) = 2j+1), `D_two`
  (D(2,j) = 2j²+2j+1), `A026002_one/two/three` (1, 7, 41), `array_formula` (any array m with the borders and the
  recurrence has 2 m(i+1,j+1) = D(i,j+2) + D(i+2,j)), `bergot_conjecture` (any such m has m(n,n) = A026002 n for
  n ≥ 1), `bergot_boundary_left`, `bergot_boundary_top`, `bergot_rec` (the recursive array meets the hypotheses),
  `bergot_diag`.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Quot.sound; Classical.choice in addition
  for the `bergot_boundary_*` and `bergot_diag`. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): the closed form for i, j ≤ 220, m(n,n) = D(n−1,n+1) = Deutsch's
  formula for n ≤ 220, and the OEIS b-file (200 terms).
- Outside Lean: reading the name "T(n,n+2)" as D(n−1, n+1) (Lean fixes a(1..3); check.py checks the b-file).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry (revision #77) and its recent history state the comment as a conjecture,
with no proof or closed form for the array. Web search found no proof. Not in google-deepmind/formal-conjectures (no
`A026002` file in the tree at HEAD) or otoi-lab/oeis-lean-proofs. The argument is short (superposition of two
shifted Delannoy arrays).
