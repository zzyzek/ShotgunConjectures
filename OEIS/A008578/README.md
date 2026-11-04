# OEIS A008578: 1 and the primes are exactly the k with sigma(k) > k·Omega(k)

**Source.** [A008578](https://oeis.org/A008578), comment by I. Gerasimova (2013): "Conjecture: the sequence
contains exactly those k such that sigma(k) > k*BigOmega(k)." (OEIS text, CC BY-SA 4.0.) A note by
R. J. Mathar in the entry says the general case needs a proof.

**Result.** True. For composite k, σ(k) ≤ k·Ω(k), with equality only at k = 6.

**Argument.** 1 and primes satisfy the inequality (σ(p) = p + 1 > p). Let k be composite with ω(k) = m
distinct primes, and q_1 < q_2 < … the primes.
- k not squarefree (Ω ≥ m + 1): σ(k)/k < ∏_{p|k} p/(p−1) ≤ ∏_{i≤m} q_i/(q_i−1) ≤ m + 1 ≤ Ω(k). The middle
  bound is by induction: q_{i+1}/(q_{i+1}−1) ≤ (i+2)/(i+1) because q_{i+1} ≥ i + 2 (base: 2 ≤ 2).
- k squarefree (m = Ω ≥ 2): σ(k)/k = ∏(1 + 1/p) ≤ ∏_{i≤m}(1 + 1/q_i) ≤ m, by induction from
  (3/2)(4/3) = 2 using 1 + 1/q_{i+1} ≤ (i+1)/i (q_{i+1} ≥ i + 2 > i). Equality needs k = 6.

**Evidence.**
- `certificate/check.py`: sieve check for k < 2·10^6; the only composite with equality is 6.
- Lean (Mathlib): [`A008578_mathlib.lean`](A008578_mathlib.lean), theorem `A008578_conjecture`: for k ≥ 1,
  (k = 1 ∨ k prime) ↔ k·Ω(k) < σ(k) (`ArithmeticFunction.cardFactors`, `sigma 1`); `composite_sigma_le`: for
  composite k, σ(k) ≤ k·Ω(k) with equality only at k = 6. Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** New. [A008578](https://oeis.org/A008578) still has the conjecture and R. J. Mathar's note that the general case needs a proof; no source found for sigma(k) <= k*Omega(k) on composites. Searched OEIS entry, references and history, web. Checked 2026-11-04.
