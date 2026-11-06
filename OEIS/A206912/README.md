# OEIS A206912: the differences of A206912 are 1s and 2s

**Source.** [A206912](https://oeis.org/A206912) (offset 1), Clark Kimberling, Feb 13 2012: position of log(n+1)
when the partial sums of the harmonic series are jointly ranked with {log(k+1)}; complement of A206911. Comment:
"Conjecture: the difference sequence of A206912 consists of 1s and 2s; see Comments at A206911." (OEIS text,
CC BY-SA 4.0, checked 2026-11-05.)

**Reading.** Write H_k = 1 + 1/2 + … + 1/k. Below log(n+1) in the joint ranking lie log 2, …, log n and the H_k
(k ≥ 1) with H_k < log(n+1), so A206912(n) = n + #{k ≥ 1 : H_k < log(n+1)}. This matches the Mathematica program
of A206911 and the data (A206912 = 1, 3, 4, 6, 7, 9, …). A tie H_k = log(n+1) cannot occur (log(n+1) is irrational
for n ≥ 1), but the proof does not need this: it holds for the definition that counts H_k strictly below.

**Result.** True. A206912(n+1) − A206912(n) ∈ {1, 2} for every n.

**Argument.**
1. *Key lemma.* For m ≥ 1 there is no k with log m ≤ H_k and H_{k+1} < log(m+1). Otherwise
   1/(k+1) = H_{k+1} − H_k < log(m+1) − log m = log(1 + 1/m) ≤ 1/m, so m ≤ k, and then
   log(m+1) ≤ log(k+1) ≤ H_k ≤ H_{k+1} < log(m+1) (using H_k ≥ log(k+1)), a contradiction.
2. *Finiteness.* H_k < log(n+1) forces k < n, since H_k ≥ log(k+1).
3. *Differences.* A206912(n+1) − A206912(n) = 1 + #{k ≥ 1 : log(n+1) ≤ H_k < log(n+2)}. H is increasing, so two
   such indices k < k' give log(n+1) ≤ H_k and H_{k+1} ≤ H_{k'} < log(n+2), which step 1 (m = n+1) excludes. So the
   count is 0 or 1.

**Evidence.**
- Lean (Mathlib): [`A206912_mathlib.lean`](A206912_mathlib.lean). `A206912 n = n + Set.ncard {k | 1 ≤ k ∧ (harmonic k : ℝ) <
  Real.log (n+1)}` (Mathlib `harmonic`). Theorems: `two_consecutive_not_between` (step 1), `lt_of_harmonic_lt`
  (step 2), `ncard_eq`, `card_new_le_one`, and `A206912_diff : A206912 (n+1) = A206912 n + 1 ∨ A206912 (n+1) =
  A206912 n + 2` for all n. Inputs from Mathlib: `log_add_one_le_harmonic`, `Real.log_le_sub_one_of_pos`.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms of every theorem: propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): floating-point ranking for n < 20000; differences are 1 or 2
  (8770 ones, 11229 twos); the complement of the computed values agrees with the A206911 data up to 141.
- Outside Lean: none. Not verified in Lean: that `A206912 n` reproduces the OEIS data terms (check.py compares
  numerically), and the irrationality of log(n+1) (not needed).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05. T. Adamczewski, *OEIS Open: How many conjectures can language models turn into
theorems?*, arXiv:2608.11941 (2026), Appendix A, proves the companion conjecture at A206911 (differences 2s and 3s);
A206911 links it, A206912 does not. The argument here uses only the standard bound H_n ≥ log(n+1). Not in
google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/206912.lean` or `206911.lean`).
