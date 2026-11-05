# Guy B2 (part): every n ≥ 2 is a sum of two deficient numbers

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B2.
Guy asks (from *Abacus*) whether every integer n > 3 is the sum of two deficient numbers, that
is, numbers m with σ(m) < 2m. OEIS [A337932](https://oeis.org/A337932) counts the representations.

**Reading.** 1 is deficient (σ(1) = 1), so the statement holds for every n ≥ 2 and is proved in
that form. The two summands are positive integers; they may be equal.

**Result.** Proved: for every n ≥ 2 there are a, b ≥ 1 with a + b = n, σ(a) < 2a and σ(b) < 2b.

**Argument.** For t ≥ 1 write rs(t) = Σ_{d ∣ t, d > 1} 1/d. Since σ(t) = Σ_{d∣t} t/d,
σ(t) = t(1 + rs(t)), so t is deficient iff rs(t) < 1 (Markov-type counting below uses only this
identity). For a family t_0, …, t_{K−1}, swapping the sums gives
Σ_k rs(t_k) = Σ_{d>1} (1/d) · #{k : d ∣ t_k}.

*Even n = 2K.* Take the K pairs (2k+1, n−2k−1), k < K. If no pair has two deficient members,
each pair has rs ≥ 1 on one side, so K ≤ Σ_k rs(2k+1) + Σ_k rs(n−2k−1) = 2 Σ_k rs(2k+1)
(the second family is the first in reverse order). A divisor d of an odd number is odd, and the
odd numbers 2k+1 ≤ 2K divisible by d number at most 2K/d. Hence
Σ_k rs(2k+1) ≤ 2K Σ_{odd d ≥ 3} 1/d² ≤ 2K (1/9 + 1/8) = 2K · 17/72, using
1/d² ≤ 1/((d−1)(d+1)) = ½(1/(d−1) − 1/(d+1)), which telescopes over odd d ≥ 5 to 1/8.
So K ≤ (34/36) K, impossible for K ≥ 1. No threshold is needed.

*Odd n ≥ 300.* Choose r ∈ {1, 5} with 3 ∤ n − 2r (r = 5 if n ≡ 2 mod 3, else r = 1); let
c = n − 2r and K = ⌊c/12⌋ ≥ 24. For k < K let m_k = 6k + r and b_k = c − 12k, so
2m_k + b_k = n, and m_k, b_k are both coprime to 6. Since m odd gives σ(2m) = 3σ(m), the number
2m_k is deficient iff rs(m_k) < 1/3. A bad pair therefore gives 1 ≤ 3 rs(m_k) + rs(b_k), and
K ≤ 3 Σ_k rs(m_k) + Σ_k rs(b_k).
Every divisor d > 1 of m_k or b_k is coprime to 6, so d ≥ 5. If d divides m_k and m_{k'}, then
d ∣ 6(k − k'), so k ≡ k' (mod d); likewise d ∣ b_k, b_{k'} gives d ∣ 12(k − k'). So d hits at
most K/d + 1 indices, and each family sum is at most
K Σ_{odd d ≥ 5} 1/d² + Σ_{5 ≤ d ≤ n, (d,6)=1} 1/d ≤ K/8 + 11/8 + (n+1)/200,
where the harmonic part is bounded by its exact value below 200 (1.3743… ≤ 11/8) plus 1/200 for
each d ≥ 200. With n + 1 ≤ 12K + 23 this gives K ≤ K/2 + 11/2 + (12K + 23)/50, i.e. K ≤ 22,
a contradiction.

*2 ≤ n < 300.* Direct check (in Lean by kernel evaluation of σ).

**Evidence.**
- Lean + Mathlib: [`B2_1_mathlib.lean`](B2_1_mathlib.lean), `B2_1_main`:
  `∀ n ≥ 2, ∃ a b, a + b = n ∧ 0 < a ∧ 0 < b ∧ σ 1 a < 2 * a ∧ σ 1 b < 2 * b`
  (Mathlib `ArithmeticFunction.sigma`). Parts: `B2_even` (all even n ≥ 2), `B2_odd` (odd n ≥ 300),
  `B2_small` (2 ≤ n < 300, `decide +kernel` in six chunks). Axioms: propext, Classical.choice,
  Quot.sound. Checked with `tools/leancheck-mathlib.sh` (exit 0, no warnings). Outside Lean: nothing.
- `certificate/constants.py`: exact rational check of 11/8, 1/8 and the K ≤ 22 threshold; every
  2 ≤ n ≤ 6000 directly; the odd-case Markov sum for odd 301 ≤ n ≤ 6000 (largest ratio to K is
  0.42, against the proved bound below 1).
- `certificate/deficient.py`: direct check of 2 ≤ n ≤ 2·10⁵ (scan triage);
  `certificate/moments.py`: empirical moment bounds behind the route.

**Review level.** `lean-proof`.

**Prior art.** 2026-11-05: web searches ("sum of two deficient numbers" proof; formal-conjectures)
and OEIS A337932 (definition, data and programs only; no positivity statement). Found only the
sums-of-two-abundant-numbers results (every n > 20161). No proof or formalisation found.
