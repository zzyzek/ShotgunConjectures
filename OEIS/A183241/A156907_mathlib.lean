import Mathlib
import OpenProblemsLib.DworkEuler

/-
OEIS A156907 (P. D. Hanna, 2009): A(x) = 1 + x exp(Σ_{k≥1} (A(2^k x) - 1)^k/k), and OEIS
A156908: the same with 3^k. Both "Conjectured to consist entirely of integers."

Definitions (q = 2 for A156907, q = 3 for A156908; the proof works for every integer q).
* Write A = 1 + x E. `bf q g m = m * [x^m] Σ_{k=1}^{m} (A(q^k x) - 1)^k / k` with
  A = 1 + x Σ_{i<m} g(i) x^i (higher coefficients do not reach x^m since k ≥ 1); `A(q^k x)` is
  `A.comp (C (q^k) * X)`.
* `e q = recSeq (bf q)`: the coefficients of E = exp(Σ_{k≥1} (A(q^k x) - 1)^k/k).
* `a q n = if n = 0 then 1 else e q (n-1)`: the coefficients of A.

Main theorems. `A156907_int n : ∃ z : ℤ, a 2 n = z`, `A156908_int n : ∃ z : ℤ, a 3 n = z`
(from `a_int q`).

Route: library `OpenProblemsLib.DworkEuler`: bf q g m = rowB F 0 W m with F = x E_N and
W(m, k) = (q^k)^m (`W1_pow`, u(k) = q^k by `LGp_zpow`, κ(m,k) = m); `rowB_gauss`, `recSeq_int`.
Not checked here: the recurrence as the OEIS "exp(...)" (standard reading); data agreement
(certificate/functional_check.py).
-/

namespace A156907

open Polynomial OpenProblemsLib.Dwork OpenProblemsLib.DworkEuler

/-- `m * [x^m] Σ_{k=1}^{m} (A(q^k x) - 1)^k / k` with `A = 1 + x Σ_{i<m} g i x^i`. -/
noncomputable def bf (q : ℤ) (g : ℕ → ℚ) (m : ℕ) : ℚ :=
  (m : ℚ) * ∑ k ∈ Finset.Icc 1 m,
    ((((1 + X * gpoly g m).comp (C ((q : ℚ) ^ k) * X) - 1) ^ k).coeff m) / (k : ℚ)

/-- Coefficients of E = exp(Σ_{k≥1} (A(q^k x) - 1)^k/k). -/
noncomputable def e (q : ℤ) : ℕ → ℚ := recSeq (bf q)

/-- Coefficients of A = 1 + x E. -/
noncomputable def a (q : ℤ) (n : ℕ) : ℚ := if n = 0 then 1 else e q (n - 1)

theorem bf_local (q : ℤ) : Local (bf q) := by
  intro g g' m h
  have : gpoly g m = gpoly g' m :=
    Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])
  simp only [bf, this]

theorem bf_eq_rowB (q : ℤ) (gz : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N) :
    bf q (fun i => (gz i : ℚ)) m =
      (rowB ((X * gpoly gz N).map C) (fun _ => 0) (fun m k => (q ^ k) ^ m) m : ℚ) := by
  rw [rowB_eq_Icc, bf, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [V_cast_map, coeff_X_mul_gpoly_pow gz N m k hm hk.2, add_comp, one_comp,
    add_sub_cancel_left, ← pow_comp, coeff_comp_C_mul_X, mul_pow, coeff_X_pow_mul']
  simp only [hk.2, ↓reduceIte]
  ring

theorem a_int (q : ℤ) (n : ℕ) : ∃ z : ℤ, a q n = z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by simp [a]⟩
  have he : ∃ z : ℤ, e q (n - 1) = z := by
    apply recSeq_int (bf q) (bf_local q)
    intro gz N
    refine ⟨rowB ((X * gpoly gz N).map C) (fun _ => 0) (fun m k => (q ^ k) ^ m), ?_, ?_⟩
    · intro p hp
      apply rowB_gauss _ _ ycond_zero _ p hp
      exact W1_pow p hp (fun k => q ^ k) (LGp_zpow p hp q) (fun m _ => m)
        (fun _ _ => rfl) (fun _ _ _ hm _ => hm)
    · intro m _ hm
      exact bf_eq_rowB q gz N m hm
  obtain ⟨z, hz⟩ := he
  exact ⟨z, by simp [a, hn.ne', hz]⟩

/-- A156907 (q = 2). -/
theorem A156907_int (n : ℕ) : ∃ z : ℤ, a 2 n = z := a_int 2 n

/-- A156908 (q = 3). -/
theorem A156908_int (n : ℕ) : ∃ z : ℤ, a 3 n = z := a_int 3 n
