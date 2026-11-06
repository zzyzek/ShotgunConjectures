# OEIS A166272: the reduced denominator is always 3

**Source.** [A166272](https://oeis.org/A166272) (A. Karttunen), "Numerator of A166100(A166101(n))/A166102(n)."
Comment: "Conjecture: equal to 3*A166100(A166101(n))/A166102(n), i.e. the denominator of the quotient
A166100(A166101(n))/A166102(n) in its reduced form is always 3." A166100(m) = S(2m+1), the sum of the
1 ≤ i ≤ 2m+1 with Jacobi symbol J(i, 2m+1) = 1; A166101 = the m with 2m+1 ∤ S(2m+1); A166102 = 2·A166101 + 1.
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True: for every odd k with k ∤ S(k), S(k)/k = t/3 in lowest terms with t = 3S(k)/k.

**Argument.** For odd k, J(4, k) = 1, so i ↦ 4i permutes the residues i mod k with J(i, k) = 1; hence
4S ≡ S and k | 3S (this is `dvd_three_S` of [`../A166103`](../A166103/README.md), settled in the same round).
Write 3S = kt. If 3 | t then k | S, contrary to the hypothesis; so gcd(t, 3) = 1 and S/k = t/3 is reduced.

**Evidence.**
- Lean (Mathlib): [`A166272_mathlib.lean`](A166272_mathlib.lean), `A166272_conjecture`: for every m with
  (2m+1) ∤ A166100 m, `((A166100 m : ℚ) / (2m+1)).den = 3` and `.num = 3·A166100 m / (2m+1)`. A166100 is defined
  from Mathlib's `jacobiSym` as in the entry; the lemmas up to `dvd_three_S` are copied from
  OEIS/A166103/A166103_mathlib.lean.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): the 92 b-file terms of A166102 and 64 of A166272 agree.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still states the conjecture; no proof found by web search. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06). The key divisibility
k | 3S(k) is the same as in the A166102/A166103 resolution of this round; the step to A166272 is immediate.
