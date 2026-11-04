import Mathlib

/-
OEIS A008676 (Mathlib): expansion of 1/((1-x^3)(1-x^5)). Conjecture (J. W. Layman, 2009):
a(n) = floor(2(n+3)/3) - floor(3(n+3)/5). README result: true for all n ≥ 0.

Main theorem `A008676_main`: in ℤ⟦X⟧ (Mathlib `PowerSeries`), the series with coefficients
R(n) = ⌊2(n+3)/3⌋ - ⌊3(n+3)/5⌋ (floors of rationals) times (1 - X^3)(1 - X^5) is 1, and every
A with A * ((1 - X^3)(1 - X^5)) = 1 has coeff n A = R(n) for all n. So R(n) is the n-th
coefficient of the g.f.

Proof. (1 - X^3)(1 - X^5) = 1 - X^3 - X^5 + X^8, so the n-th coefficient of the product is
R(n) - R(n-3) - R(n-5) + R(n-8) (missing terms 0 for small n, `coeff_mul_X_pow'`). This is
[n = 0]: for n < 8 by evaluation, for n ≥ 8 by the recurrence R(n+8) = R(n+5) + R(n+3) - R(n)
(`rhs_rec` of the core file A008676.lean, omega per residue mod 15). Uniqueness of inverses
in a commutative ring gives the rest. ⌊m/d⌋ = m / d (Int division) by
`Rat.floor_intCast_div_natCast`.

Outside Lean: nothing.
-/

open PowerSeries

def A008676_rhs (n : ℕ) : ℤ := 2 * ((n : ℤ) + 3) / 3 - 3 * ((n : ℤ) + 3) / 5

theorem A008676_rhs_rec (n : ℕ) :
    A008676_rhs (n + 8) = A008676_rhs (n + 5) + A008676_rhs (n + 3) - A008676_rhs n := by
  unfold A008676_rhs
  have h : n % 15 = 0 ∨ n % 15 = 1 ∨ n % 15 = 2 ∨ n % 15 = 3 ∨ n % 15 = 4 ∨
      n % 15 = 5 ∨ n % 15 = 6 ∨ n % 15 = 7 ∨ n % 15 = 8 ∨ n % 15 = 9 ∨
      n % 15 = 10 ∨ n % 15 = 11 ∨ n % 15 = 12 ∨ n % 15 = 13 ∨ n % 15 = 14 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> push_cast <;> omega

theorem A008676_rhs_floor (n : ℕ) :
    A008676_rhs n = ⌊(2 * ((n : ℚ) + 3)) / 3⌋ - ⌊(3 * ((n : ℚ) + 3)) / 5⌋ := by
  have e1 : (2 * ((n : ℚ) + 3)) / 3 = ((2 * ((n : ℤ) + 3) : ℤ) : ℚ) / ((3 : ℕ) : ℚ) := by
    push_cast; ring
  have e2 : (3 * ((n : ℚ) + 3)) / 5 = ((3 * ((n : ℤ) + 3) : ℤ) : ℚ) / ((5 : ℕ) : ℚ) := by
    push_cast; ring
  rw [e1, e2, Rat.floor_intCast_div_natCast, Rat.floor_intCast_div_natCast]
  rfl

theorem A008676_mul_eq_one :
    PowerSeries.mk (fun n => A008676_rhs n) * ((1 - X ^ 3) * (1 - X ^ 5)) = (1 : ℤ⟦X⟧) := by
  have hD : ((1 : ℤ⟦X⟧) - X ^ 3) * (1 - X ^ 5) = 1 - X ^ 3 - X ^ 5 + X ^ 8 := by ring
  rw [hD]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mul_X_pow', coeff_mk,
    coeff_one]
  rcases Nat.lt_or_ge n 8 with h | h
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show 3 ≤ m + 8 by omega, show 5 ≤ m + 8 by omega, show 8 ≤ m + 8 by omega,
      ite_true, show m + 8 ≠ 0 by omega, ite_false, show m + 8 - 3 = m + 5 by omega,
      show m + 8 - 5 = m + 3 by omega, show m + 8 - 8 = m by omega]
    rw [A008676_rhs_rec]
    ring

theorem A008676_main :
    PowerSeries.mk (fun n => (⌊(2 * ((n : ℚ) + 3)) / 3⌋ - ⌊(3 * ((n : ℚ) + 3)) / 5⌋ : ℤ)) *
        ((1 - X ^ 3) * (1 - X ^ 5)) = (1 : ℤ⟦X⟧) ∧
    ∀ A : ℤ⟦X⟧, A * ((1 - X ^ 3) * (1 - X ^ 5)) = 1 →
      ∀ n : ℕ, coeff n A = ⌊(2 * ((n : ℚ) + 3)) / 3⌋ - ⌊(3 * ((n : ℚ) + 3)) / 5⌋ := by
  have hB := A008676_mul_eq_one
  have hfun : (fun n : ℕ => (⌊(2 * ((n : ℚ) + 3)) / 3⌋ - ⌊(3 * ((n : ℚ) + 3)) / 5⌋ : ℤ)) =
      fun n => A008676_rhs n := by
    funext n; rw [A008676_rhs_floor]
  rw [hfun]
  refine ⟨hB, fun A hA n => ?_⟩
  have hAB : A = PowerSeries.mk (fun n => A008676_rhs n) := by
    linear_combination (-A) * hB + (PowerSeries.mk (fun n => A008676_rhs n)) * hA
  rw [hAB, coeff_mk, A008676_rhs_floor]
