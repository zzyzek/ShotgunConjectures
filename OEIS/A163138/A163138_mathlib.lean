import Mathlib
import OpenProblemsLib.DworkEuler

/-
OEIS A163138 (P. D. Hanna, 2009): A(x) = exp(Σ_{n≥1} (2^n + A(x))^n x^n/n).
Conjecture: for every integer q, A(x,q) = exp(Σ_{n≥1} (q^n + A(x,q))^n x^n/n) has integer
coefficients.

Definitions.
* `bf q g m = m * [x^m] Σ_{n=1}^{m} (q^n + A)^n x^n / n` with A = Σ_{i<m} g(i) x^i (higher
  coefficients do not reach x^m since n ≥ 1).
* `a q = recSeq (bf q)`: a(0) = 1, (N+1) a(N+1) = Σ_{j=0..N} bf a (j+1) a(N-j) (coefficients
  of exp).

Main theorems. `A163138_conjecture (q : ℤ) n : ∃ z : ℤ, a q n = z`; `A163138_int` (q = 2).

Route (three-variable form): library `OpenProblemsLib.DworkEuler` with F = X (Y + A_N) in
ℤ[Y][X], evaluation points y(n) = q^n (`ycond_pow`) and weights W = 1 (`W1_one`):
bf q g m = rowB F y 1 m (`V_cast_eval`), then `rowB_gauss`, `recSeq_int`.
Not checked here: the recurrence as the OEIS "exp(...)" (standard reading); data agreement
(certificate/check.py).
-/

namespace A163138

open Polynomial OpenProblemsLib.Dwork OpenProblemsLib.DworkEuler

/-- `m * [x^m] Σ_{n=1}^{m} (q^n + A)^n x^n / n` with `A = Σ_{i<m} g i x^i`. -/
noncomputable def bf (q : ℤ) (g : ℕ → ℚ) (m : ℕ) : ℚ :=
  (m : ℚ) * ∑ n ∈ Finset.Icc 1 m,
    (((C ((q : ℚ) ^ n) + gpoly g m) ^ n * X ^ n).coeff m) / (n : ℚ)

/-- Coefficients of A(x, q) = exp(Σ_{n≥1} (q^n + A)^n x^n/n). -/
noncomputable def a (q : ℤ) : ℕ → ℚ := recSeq (bf q)

theorem bf_local (q : ℤ) : Local (bf q) := by
  intro g g' m h
  have : gpoly g m = gpoly g' m :=
    Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])
  simp only [bf, this]

/-- `F = X (Y + A_N)` in `ℤ[Y][X]`. -/
noncomputable def F (gz : ℕ → ℤ) (N : ℕ) : Polynomial (Polynomial ℤ) :=
  X * (C Polynomial.X + (gpoly gz N).map C)

theorem F_eval (gz : ℕ → ℤ) (N : ℕ) (y : ℤ) :
    (F gz N).map (evalRingHom y) = X * (C y + gpoly gz N) := by
  have h : ((gpoly gz N).map C).map (evalRingHom y) = gpoly gz N := by
    rw [Polynomial.map_map]
    have : (evalRingHom y).comp (C : ℤ →+* Polynomial ℤ) = RingHom.id ℤ := by ext; simp
    rw [this, Polynomial.map_id]
  simp [F, Polynomial.map_mul, Polynomial.map_add, h]

theorem bf_eq_rowB (q : ℤ) (gz : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N) :
    bf q (fun i => (gz i : ℚ)) m = (rowB (F gz N) (fun n => q ^ n) (fun _ _ => 1) m : ℚ) := by
  rw [rowB_eq_Icc, bf, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [V_cast_eval, F_eval]
  have h1 : ((((X * (C (q ^ n) + gpoly gz N)) ^ n).coeff m : ℤ) : ℚ) =
      ((X * (C ((q : ℚ) ^ n) + gpoly (fun i => (gz i : ℚ)) N)) ^ n).coeff m := by
    rw [← map_gpoly]
    have : X * (C ((q : ℚ) ^ n) + (gpoly gz N).map (Int.castRingHom ℚ)) =
        (X * (C (q ^ n) + gpoly gz N)).map (Int.castRingHom ℚ) := by simp
    rw [this, ← Polynomial.map_pow, coeff_map]; simp
  have h2 : ((X * (C ((q : ℚ) ^ n) + gpoly (fun i => (gz i : ℚ)) N)) ^ n).coeff m =
      ((X * (C ((q : ℚ) ^ n) + gpoly (fun i => (gz i : ℚ)) m)) ^ n).coeff m :=
    coeff_X_mul_pow_congr _ _ m n (fun i hi => by
      rw [coeff_add, coeff_add, coeff_gpoly, coeff_gpoly]
      simp [hi, show i < N by omega])
  rw [h1, h2, mul_pow, mul_comm (X ^ n)]
  ring

theorem A163138_conjecture (q : ℤ) (n : ℕ) : ∃ z : ℤ, a q n = z := by
  apply recSeq_int (bf q) (bf_local q)
  intro gz N
  refine ⟨rowB (F gz N) (fun n => q ^ n) (fun _ _ => 1), ?_, ?_⟩
  · intro p hp
    exact rowB_gauss _ _ (ycond_pow q) _ p hp (W1_one p)
  · intro m _ hm
    exact bf_eq_rowB q gz N m hm

/-- A163138 itself (q = 2). -/
theorem A163138_int (n : ℕ) : ∃ z : ℤ, a 2 n = z := A163138_conjecture 2 n
