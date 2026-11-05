# OEIS A005430: the inverse binomial transform of n·C(2n,n) is 2·A132894(n)

**Source.** OEIS [A005430](https://oeis.org/A005430) (Apéry numbers n·C(2n,n), offset 0), comment by
R. J. Mathar (Oct 21 2012): "Conjecture: the terms of the inverse binomial transform are 2*A132894(n)."
(OEIS text, CC BY-SA 4.0; still marked "Conjecture" on 2026-11-05.)

**Reading.** Inverse binomial transform b(n) = Σ_{k=0..n} (−1)^(n−k) C(n,k) A005430(k).
A132894(n) is defined as the number of H steps in all length-n left factors of Motzkin paths; the entry's
first formula is A132894(n) = Σ_k k C(n,k) C(n−k, ⌊(n−k)/2⌋) (place the k H steps, then a left factor of a
Dyck path on the other n−k steps, of which there are C(n−k, ⌊(n−k)/2⌋)). The Lean file uses this formula.

**Result.** True for every n ≥ 0: b(n) = 2·A132894(n) (0, 2, 8, 30, 104, 350, ...).

Side finding: W. Zudilin's formula printed in A132894, "a(n) = Sum_{k=0..n} k*C(n,k)*C(2*k,k)*(-1)^(n-k)", is
exactly the inverse binomial transform above, so it equals 2·A132894(n), not A132894(n) (n = 1 gives 2, not 1).

**Argument.** For n = m+1 ≥ 1, k·C(n,k) = n·C(m,k−1) and C(2j+2,j+1) = 2·C(2j+1,j) give
b(n) = 2n Σ_j (−1)^(m−j) C(m,j) C(2j+1,j) and A132894(n) = n Σ_j C(m,j) C(j,⌊j/2⌋).
Both sums equal [x^m] (1+x)(1+x+x²)^m:
- 1+x+x² = (1+x)² − x: the term j contributes (−1)^(m−j) C(m,j) [x^j](1+x)^(2j+1) = (−1)^(m−j) C(m,j) C(2j+1,j);
- 1+x+x² = x + (1+x²): the term j contributes C(m,j)([x^j] + [x^(j−1)])(1+x²)^j = C(m,j) C(j,⌊j/2⌋).
n = 0: both sides 0.

**Evidence.**
- Lean (Mathlib): [`A005430_mathlib.lean`](A005430_mathlib.lean). `A005430_conjecture (n : ℕ) :
  A005430_invbin n = 2 * A132894 n`; supporting `A005430_left`, `A005430_right` (the two coefficient
  extractions), `A005430_coeff_sq`, `A005430_choose_two`; `A005430_data` (terms of both sides by `decide`).
  Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: identity for n < 200, the coefficient form, brute-force check of the A132894 formula
  against its path definition for n ≤ 12, and the factor 2 in Zudilin's formula.
- Outside Lean: that the formula Σ k C(n,k) C(n−k,⌊(n−k)/2⌋) counts A132894's paths (standard, checked by
  enumeration for n ≤ 12).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: OEIS A005430 and A132894 entries, web search, google-deepmind/formal-conjectures
(no A005430/A132894 file). The entries carry P. Luschny's e.g.f.s (Aug 2012) exp(2x)·2x(I₀(2x)+I₁(2x)) and
exp(x)·x(I₀(2x)+I₁(2x)); the inverse binomial transform multiplies an e.g.f. by e^(−x), so the conjecture follows
at once from those two printed (unproved in the entry) formulas. No written proof found.
