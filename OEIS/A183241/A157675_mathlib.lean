import Mathlib
import OpenProblemsLib.DworkEuler

/-
OEIS A157675 (P. D. Hanna, 2009): A(x) = exp(Σ_{n≥1} A(2^n x)^n x^n/n). "Conjectured to consist
entirely of integers."

Definitions.
* `bf g m = m * [x^m] Σ_{n=1}^{m} A(2^n x)^n x^n / n` with A = Σ_{i<m} g(i) x^i (higher
  coefficients of A do not reach x^m since n ≥ 1); `A(2^n x)` is `A.comp (C (2^n) * X)`.
* `a = recSeq bf`: a(0) = 1, (N+1) a(N+1) = Σ_{j=0..N} bf a (j+1) a(N-j) (coefficients of exp).

Main theorem. `A157675_int n : ∃ z : ℤ, a n = z`.

Route: library `OpenProblemsLib.DworkEuler`: bf g m = rowB F 0 W m with F = x A_N and
W(m, n) = (2^n)^(m-n) (`W1_pow`, u(n) = 2^n a Gauss sequence by `LGp_zpow`); `rowB_gauss`,
`recSeq_int`. Not checked here: the recurrence as the OEIS "exp(...)" (standard reading); data
agreement (certificate/functional_check.py).
-/

namespace A157675

open Polynomial OpenProblemsLib.Dwork OpenProblemsLib.DworkEuler

/-- `m * [x^m] Σ_{n=1}^{m} A(2^n x)^n x^n / n` with `A = Σ_{i<m} g i x^i`. -/
noncomputable def bf (g : ℕ → ℚ) (m : ℕ) : ℚ :=
  (m : ℚ) * ∑ n ∈ Finset.Icc 1 m,
    ((((gpoly g m).comp (C ((2 : ℚ) ^ n) * X)) ^ n * X ^ n).coeff m) / (n : ℚ)

/-- Coefficients of A(x) = exp(Σ_{n≥1} A(2^n x)^n x^n/n). -/
noncomputable def a : ℕ → ℚ := recSeq bf

theorem bf_local : Local bf := by
  intro g g' m h
  have : gpoly g m = gpoly g' m :=
    Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])
  simp only [bf, this]

theorem bf_eq_rowB (gz : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N) :
    bf (fun i => (gz i : ℚ)) m =
      (rowB ((X * gpoly gz N).map C) (fun _ => 0) (fun m n => ((2 : ℤ) ^ n) ^ (m - n)) m : ℚ) := by
  rw [rowB_eq_Icc, bf, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  rw [V_cast_map, coeff_X_mul_gpoly_pow gz N m n hm hn.2, coeff_mul_X_pow', ← pow_comp,
    coeff_comp_C_mul_X]
  simp only [hn.2, ↓reduceIte]
  ring

theorem A157675_int (n : ℕ) : ∃ z : ℤ, a n = z := by
  apply recSeq_int bf bf_local
  intro gz N
  refine ⟨rowB ((X * gpoly gz N).map C) (fun _ => 0) (fun m n => ((2 : ℤ) ^ n) ^ (m - n)), ?_, ?_⟩
  · intro p hp
    apply rowB_gauss _ _ ycond_zero _ p hp
    exact W1_pow p hp (fun n => (2 : ℤ) ^ n) (LGp_zpow p hp 2) (fun m n => m - n)
      (fun m n => (Nat.mul_sub p m n).symm) (fun k m n hm hn => Nat.dvd_sub hm hn)
  · intro m _ hm
    exact bf_eq_rowB gz N m hm
