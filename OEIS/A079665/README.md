# OEIS A079665: when is (b^s + 1)/(b^r + 1) an integer

**Source.** [A079665](https://oeis.org/A079665), comment: "Conjecture: (b^s+1)/(b^r+1) is an integer if and
only if: 1) r<s/2, 2) if s==1 (mod 2) then r is divisor of s, 3) if s=k*2^t with gcd(k,2^t)=1 then r is
2^t*u with u dividing k" (OEIS text, CC BY-SA 4.0.)

**Reading.** b ≥ 2 and 1 ≤ r < s (the rows of A079665 have r ≤ s − 1).

**Result.** True; classical.

**Argument.** Write s = qr + ρ, 0 ≤ ρ < r. Since b^r ≡ −1 (mod b^r + 1), b^s + 1 ≡ (−1)^q b^ρ + 1. For
ρ = 0 this is 0 iff q is odd. For ρ > 0 it is b^ρ + 1 or 1 − b^ρ, both nonzero with absolute value
< b^r + 1. So b^r + 1 | b^s + 1 iff r | s and s/r is odd. With s = k·2^t (k odd) that says r = 2^t·u with
u | k, which is condition 3; then s/r ≥ 3 gives condition 1, and condition 2 is the case t = 0 of 3.

**Evidence.**
- Lean (Mathlib): [`A079665_mathlib.lean`](A079665_mathlib.lean) proves `A079665_classical` (b ≥ 2, r ≥ 1: b^r + 1 ∣ b^s + 1 ↔ r ∣ s ∧ s/r odd) and `A079665_main` (for b ≥ 2, 1 ≤ r < s: divisibility ↔ 2r < s ∧ (s odd → r ∣ s) ∧ ∀ t k, gcd(k, 2^t) = 1 → s = k·2^t → ∃ u, r = 2^t·u ∧ u ∣ k). Outside Lean: nothing.
- `certificate/check.py`: divisibility, "r | s with s/r odd" and the three conditions agree for
  b = 2..12, s ≤ 60.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`A079665_mathlib.lean`](A079665_mathlib.lean)).
**Prior art.** Known: b^r + 1 divides b^s + 1 iff r | s with s/r odd (classical divisibility lemma). [A079665](https://oeis.org/A079665) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
