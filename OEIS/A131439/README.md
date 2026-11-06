# OEIS A131439: 1, 7, then 4k + 14, and its inverse binomial transform

**Source.** [A131439](https://oeis.org/A131439) (offset 1), Gary W. Adamson, Jul 11 2007: "Inverse binomial
transform of A131438 (assuming zero offset in both sequences)". Comments: "Conjecture: The sequence appears to be
(1, 7, ...) followed by 4k + 14; k=0,1,2,..." and "Inverse binomial transform of this sequence = (1, 6, 1, -4, 7,
-10, 13, -16, 19, -22, ...)". [A131438](https://oeis.org/A131438) is defined by a(n) = (2+n)·2^n − 2 − 3n
(offset 1; definition replaced by this formula by R. J. Mathar, 2011). (OEIS text, CC BY-SA 4.0, A131439
revision #21 of Mar 23 2026, A131438 revision #14 of Oct 17 2025, checked 2026-11-06.)

**Reading.** With zero offset, b(k) = A131438(k+1) for k ≥ 0 and A131439(m+1) = Σ_{k=0..m} (−1)^(m−k) C(m,k) b(k).
The entry's example (1,3,3,1)·(1,7,14,18) = 82 = A131438(4) confirms this. The second comment is read the same way
(zero offset). The example in A131438, "a(3) = 19 = ... (7 + 9 + 13)", disagrees with its data and formula
(a(3) = 29); it does not affect A131439, which uses the formula.

**Result.** True. A131439 = 1, 7, then A131439(n) = 4n + 2 for n ≥ 3 (that is 4k + 14 with k = n − 3). Its
inverse binomial transform is 1, 6, then (−1)^m (3m − 5) for m ≥ 2.

**Argument.**
1. The inverse binomial transform of f at m is the m-th forward difference Δ^m f(0).
2. b(k) = (k+3)·2^(k+1) − 2 − 3(k+1) = (2k+6)·2^k − 3k − 5. Then Δb(k) = (2k+10)·2^k − 3 and
   Δ²b(k) = (2k+14)·2^k. For g_A(k) = (2k+A)·2^k, Δg_A = g_{A+4}. So Δ^m b = g_{4m+6} for m ≥ 2 and
   A131439(m+1) = Δ^m b(0) = 4m + 6; directly, A131439(1) = 1 and A131439(2) = 7.
3. So c(m) = A131439(m+1) = (4m+6) − 3·[m = 1] − 5·[m = 0]. The inverse binomial transform is linear; it sends
   4m+6 to 0 for m ≥ 2 (second difference of a linear function) and the point mass v·[k = i] to
   (−1)^(m−i) C(m,i) v. For m ≥ 2 this gives −3·(−1)^(m−1) m − 5·(−1)^m = (−1)^m (3m − 5); m = 0, 1 give 1, 6.

**Evidence.**
- Lean (Mathlib): [`A131439_mathlib.lean`](A131439_mathlib.lean). Definitions `A131438 n = (2+n) 2^n − 2 − 3n`,
  `b k` with `b_eq : b k = A131438 (k+1)`, `invBinom f m = Σ_{k ≤ m} (−1)^(m−k) C(m,k) f k`,
  `A131439 n = invBinom b (n−1)`. Theorems: `A131439_one`, `A131439_two`, `A131439_closed : 3 ≤ n → A131439 n =
  4n + 2`; `invBinom_c_zero`, `invBinom_c_one`, `invBinom_c : 2 ≤ m → invBinom c m = (−1)^m (3m − 5)` with
  `c m = A131439 (m+1)`. Uses Mathlib `fwdDiff_iter_eq_sum_shift`.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Classical.choice, Quot.sound (some
  theorems fewer). No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): exact integers, 200 terms; the 45 OEIS data terms, the closed
  form and the second comment agree.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data beyond n ≤ 2 (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry has carried Colin Barker's recurrence a(n) = 2a(n−1) − a(n−2) for
n > 4 and g.f. −x(x+1)(3x²−4x−1)/(x−1)² since Jan 06 2013, stated without proof; they are equivalent to the
conjecture. The cross-reference "Essentially the same as A073760" (4n + 2) says the same. The argument is a routine
finite-difference computation. Not in google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/131439.lean`)
or otoi-lab/oeis-lean-proofs; a web search found no proof.
