import Mathlib

/-
COM-C184 (Mathlib). Coman, conjecture 184: for every Poulet number P, P - 5 is a sum of
distinct powers of 2. README result: true and trivial (binary expansion).

Main theorem `C184_main`: for every Poulet number P (Mathlib `Nat.FermatPsp P 2`: composite,
P > 1, P ∣ 2^(P-1) - 1) we have 5 < P, and there is a finite set S of exponents with
∑_{i ∈ S} 2^i = P - 5. The set S is the set of binary digit positions of P - 5
(Mathlib `Nat.bitIndices`); 5 < P holds because 2, 3, 5 are prime and 4 ∤ 2^3 - 1.
This is the README result in full.

Outside Lean: nothing.
-/

theorem C184_gt_five (P : ℕ) (h : P.FermatPsp 2) : 5 < P := by
  obtain ⟨hpp, hnp, h1⟩ := h
  unfold Nat.ProbablePrime at hpp
  by_contra hc
  interval_cases P <;> simp_all <;> norm_num at hnp

theorem C184_main (P : ℕ) (h : P.FermatPsp 2) :
    5 < P ∧ ∃ S : Finset ℕ, ∑ i ∈ S, 2 ^ i = P - 5 :=
  ⟨C184_gt_five P h, ⟨(P - 5).bitIndices.toFinset, Finset.sum_toFinset_bitIndices_two_pow _⟩⟩
