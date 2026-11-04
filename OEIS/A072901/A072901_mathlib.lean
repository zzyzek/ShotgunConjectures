import Mathlib
import OpenProblemsLib.R5_Quadratic

/-
OEIS-A072901 (Mathlib). A072901: composite n such that the discriminant of Q(√n) is 4n.
Conjecture (V. Librandi, M. Marcus): all terms are squarefree. README result: true; trivial.

The field Q(√n) is Mathlib's `QuadraticAlgebra ℚ n 0` (ℚ[ω] with ω² = n), a field when n is
not a square in ℚ (hypothesis `[Fact (¬ IsSquare (n : ℚ))]`, equivalent to ¬ IsSquare n by
`Rat.isSquare_natCast_iff`). Its discriminant is Mathlib's `NumberField.discr`, the
discriminant of a ℤ-basis of the ring of integers `𝓞 K`.

Main theorem `A072901_discr`: for every natural n that is not a square,
NumberField.discr Q(√n) = 4n iff n is squarefree and n ≡ 2 or 3 (mod 4).
`A072901_conjecture`: hence every composite n with disc Q(√n) = 4n is squarefree, which is
the README result.

Proof. Write n = s²·d with d squarefree (`Nat.sq_mul_squarefree`); Q(√n) ≅ Q(√d) as ℚ-algebras
(Mathlib's classification of quadratic algebras by discriminant up to squares). The library
`OpenProblemsLib.R5Quadratic.discr_sqrt` (module R5_Quadratic) computes NumberField.discr Q(√d) = d (d ≡ 1 mod 4)
or 4d (otherwise) by showing the ring of integers is Z[(1+√d)/2] resp. Z[√d]. Then 4n = d or
4d forces s = 1.

`A072901_main` (earlier version) states the same arithmetic for Mathlib's fundamental
discriminants `Int.IsFundamentalDiscr`.

Nothing of the README result is outside Lean.
-/

open OpenProblemsLib.R5Quadratic

theorem A072901_main (n : ℕ) :
    Int.IsFundamentalDiscr (4 * (n : ℤ)) ↔ Squarefree n ∧ (n % 4 = 2 ∨ n % 4 = 3) := by
  rw [Int.isFundamentalDiscr_four_mul, Int.squarefree_natCast]
  exact and_congr_right (fun _ => by omega)

/-- disc Q(√n) = 4n iff n is squarefree and n ≡ 2, 3 (mod 4), for n not a square. -/
theorem A072901_discr (n : ℕ) [Fact (¬ IsSquare (n : ℚ))] :
    NumberField.discr (QuadraticAlgebra ℚ (n : ℚ) 0) = 4 * n ↔
      Squarefree n ∧ (n % 4 = 2 ∨ n % 4 = 3) := by
  obtain ⟨s, d, rfl, hd⟩ := exists_sq_mul_squarefree n
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact Fact.out (p := ¬ IsSquare (((0 ^ 2 * d : ℕ)) : ℚ)) ⟨0, by simp⟩
  have hdi : Squarefree (d : ℤ) := Int.squarefree_natCast.mpr hd
  have : Fact (¬ IsSquare ((d : ℤ) : ℚ)) := ⟨fun ⟨r, hr⟩ =>
    Fact.out (p := ¬ IsSquare (((s ^ 2 * d : ℕ)) : ℚ))
      ⟨s * r, by push_cast at hr ⊢; rw [hr]; ring⟩⟩
  obtain ⟨e⟩ : Nonempty (QuadraticAlgebra ℚ (((s ^ 2 * d : ℕ)) : ℚ) 0 ≃ₐ[ℚ]
      QuadraticAlgebra ℚ ((d : ℤ) : ℚ) 0) := by
    let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
    rw [QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two]
    refine ⟨Units.mk0 (s : ℚ) (by exact_mod_cast hs0), ?_⟩
    rw [QuadraticAlgebra.discr_def, QuadraticAlgebra.discr_def, Units.val_mk0]
    push_cast
    ring
  rw [NumberField.discr_eq_discr_of_algEquiv _ e, discr_sqrt hdi]
  have h4 : d % 4 ≠ 0 := by
    intro h
    have := hd 2 ⟨d / 4, by omega⟩
    simp at this
  rcases (show s = 1 ∨ 2 ≤ s by omega) with rfl | hs2
  · simp only [one_pow, one_mul, hd, true_and]
    split_ifs with h <;> omega
  · have hns : ¬ Squarefree (s ^ 2 * d) := fun h => by
      have := h s ⟨d, by ring⟩
      rw [Nat.isUnit_iff] at this
      omega
    simp only [hns, false_and, iff_false]
    have hs4 : (4 : ℤ) ≤ (s : ℤ) ^ 2 := by
      have : (2 : ℤ) ≤ s := by exact_mod_cast hs2
      nlinarith
    have hdpos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd.ne_zero
    push_cast
    split_ifs <;> intro h <;> nlinarith

/-- The conjecture: composite n with disc Q(√n) = 4n are squarefree. -/
theorem A072901_conjecture (n : ℕ) (_hn : 1 < n) (_hc : ¬ n.Prime) [Fact (¬ IsSquare (n : ℚ))]
    (hd : NumberField.discr (QuadraticAlgebra ℚ (n : ℚ) 0) = 4 * n) : Squarefree n :=
  ((A072901_discr n).mp hd).1
