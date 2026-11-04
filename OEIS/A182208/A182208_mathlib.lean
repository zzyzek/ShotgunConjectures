import OpenProblemsLib

/-
OEIS A182208 (Mathlib). Conjecture (Coman 2012): any Carmichael number C divisible by 7 can
be written as 7(6m+1)(6n+1) or 7(6m−1)(6n−1); in other words there are no Carmichael numbers
divisible by 7 of the form 7(6m+1)(6n−1). README result: true.

Main theorem `A182208_main`: for every Carmichael number C (Mathlib `Nat.IsCarmichael`) with
7 ∣ C, (1) C = 7 d e for some d, e > 1 with d ≡ e ≡ 1 or d ≡ e ≡ 5 (mod 6), and (2) every
factorization C = 7 d e has d ≡ e ≡ 1 or d ≡ e ≡ 5 (mod 6). Corollary `A182208_no_mixed`:
7(6m+1)(6n−1) is never a Carmichael number (natural subtraction; n = 0 gives 0).
Proof: Korselt's criterion in the necessary direction (Mathlib
`Nat.IsCarmichael.prime_sub_one_dvd`) gives 6 ∣ C − 1, so C/7 ≡ 1 (mod 6); C/7 is composite
because a Carmichael number has at least three prime factors (Mathlib
`Nat.IsCarmichael.three_le_card_primeFactors`); the residue split is the core-Lean `split`
of `A182208.lean` (copied below in namespace `Core`).

Outside Lean: nothing. (Generated from certificate/A182208_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-! ### Core-Lean facts, copied verbatim from `A182208.lean` -/
namespace Core
  theorem cofactor (C : Nat) (h7 : C % 7 = 0) (h6 : C % 6 = 1) : (C / 7) % 6 = 1 := by omega

  theorem residues : ∀ r, r < 6 → ∀ s, s < 6 → (r * s) % 6 = 1 →
      (r = 1 ∧ s = 1) ∨ (r = 5 ∧ s = 5) := by decide

  theorem split (d e : Nat) (h : (d * e) % 6 = 1) :
      (d % 6 = 1 ∧ e % 6 = 1) ∨ (d % 6 = 5 ∧ e % 6 = 5) := by
    rw [Nat.mul_mod] at h
    exact residues (d % 6) (Nat.mod_lt _ (by decide)) (e % 6) (Nat.mod_lt _ (by decide)) h
end Core

theorem split_of_carmichael (C : ℕ) (h : C.IsCarmichael) (h7 : 7 ∣ C) (d e : ℕ)
    (hC : C = 7 * d * e) : (d % 6 = 1 ∧ e % 6 = 1) ∨ (d % 6 = 5 ∧ e % 6 = 5) := by
  have k : 6 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h7
  have := h.two_lt
  apply Core.split
  rw [mul_assoc] at hC
  generalize d * e = x at hC ⊢
  omega

theorem A182208_main (C : ℕ) (h : C.IsCarmichael) (h7 : 7 ∣ C) :
    (∃ d e, 1 < d ∧ 1 < e ∧ C = 7 * d * e ∧ ((d % 6 = 1 ∧ e % 6 = 1) ∨ (d % 6 = 5 ∧ e % 6 = 5))) ∧
    (∀ d e, C = 7 * d * e → (d % 6 = 1 ∧ e % 6 = 1) ∨ (d % 6 = 5 ∧ e % 6 = 5)) := by
  refine ⟨?_, split_of_carmichael C h h7⟩
  obtain ⟨c, rfl⟩ := h7
  have h3 := h.three_le_card_primeFactors
  have hc0 : c ≠ 0 := by rintro rfl; simpa using h.two_lt
  have hc2 : 2 ≤ c := by
    by_contra hlt
    have : c = 1 := by omega
    subst this
    exact h.not_prime (by norm_num)
  have hcp : ¬ c.Prime := by
    intro hp
    rw [Nat.primeFactors_mul (by norm_num) hc0, Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors hp] at h3
    have := Finset.card_union_le ({7} : Finset ℕ) {c}
    simp only [Finset.card_singleton] at this
    omega
  have hlt : c.minFac < c := (Nat.not_prime_iff_minFac_lt hc2).mp hcp
  have hmf : 1 < c.minFac := (Nat.minFac_prime (by omega)).one_lt
  obtain ⟨e, he⟩ := Nat.minFac_dvd c
  have he1 : 1 < e := by
    by_contra hle
    have : e ≤ 1 := by omega
    interval_cases e <;> simp at he <;> omega
  refine ⟨c.minFac, e, hmf, he1, by rw [mul_assoc, ← he], ?_⟩
  exact split_of_carmichael _ h ⟨c, rfl⟩ _ _ (by rw [mul_assoc, ← he])

theorem A182208_no_mixed (m n : ℕ) : ¬ (7 * (6 * m + 1) * (6 * n - 1)).IsCarmichael := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using h.two_lt
  have := split_of_carmichael _ h (by rw [mul_assoc]; exact Dvd.intro _ rfl) _ _ rfl
  omega
