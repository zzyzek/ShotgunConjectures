# OEIS A226187: a(n+1)/a(n) → exp(1/3)

**Source.** [A226187](https://oeis.org/A226187) (offset 1), Clark Kimberling, May 30 2013: least positive integer k
such that 1 + 1/2 + … + 1/k > n/3. Comment: conjecture that a(n+1)/a(n) converges to 1.39…, probably exp(1/3).
(OEIS text, CC BY-SA 4.0, checked 2026-11-05.)

**Result.** True: a(n+1)/a(n) → exp(1/3) = 1.39561…

**Argument.** Let H_k = 1 + … + 1/k and a = a(n).
1. Since H_0 = 0 ≤ n/3, a ≥ 1, and by minimality H_{a−1} ≤ n/3 < H_a, so 0 < H_a − n/3 ≤ 1/a.
2. a(n) → ∞: H is increasing, so a(n) < N gives n/3 < H_N, i.e. n < 3 H_N.
3. H_k − log k → γ (Euler's constant). So log a(n) − n/3 = (H_a − n/3) − (H_a − log a) → 0 − γ.
4. Hence log a(n+1) − log a(n) = [log a(n+1) − (n+1)/3] − [log a(n) − n/3] + 1/3 → 1/3, and the ratio
   a(n+1)/a(n) = exp(log a(n+1) − log a(n)) → exp(1/3).

**Evidence.**
- Lean (Mathlib): [`A226187_mathlib.lean`](A226187_mathlib.lean). `A226187 n = Nat.find (exists_harmonic_gt n)`, the
  least k with (n : ℚ)/3 < harmonic k (least natural and least positive agree, `a_pos`). Theorems: `a_spec`,
  `a_prev`, `a_upper` (step 1), `a_tendsto` (step 2), and
  `A226187_ratio : Tendsto (fun n => (A226187 (n+1) : ℝ) / A226187 n) atTop (𝓝 (Real.exp (1/3)))`.
  Input from Mathlib: `Real.tendsto_harmonic_sub_log`, `log_add_one_le_harmonic`.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms of every theorem: propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): exact rational computation of a(1..40) (a(10) = 16 as in the
  entry's example, a(3) = 2 as corrected in the entry); ratio at n = 39 is 1.3956127 against exp(1/3) = 1.3956124.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data terms (check.py), and no rate of
  convergence is extracted.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05. Standard: H_k = log k + γ + O(1/k) (Euler–Maclaurin), cf. A004080 and A002387,
which the entry's later comment cites. The sister entry A226188 records the same expansion confirming exp(2/3)
(J.-F. Alcover, 2013). No other written proof found for A226187. Not in google-deepmind/formal-conjectures
(no `FormalConjectures/OEIS/226187.lean`).
