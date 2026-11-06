import Mathlib
import OpenProblemsLib.DworkEuler

/-
OEIS A163921 (P. D. Hanna, 2009): g.f. A(x) = exp(Σ_{n≥1} A(σ(n) x)^n x^n/n).
Conjecture: if exp(Σ L(n) x^n/n) is an integer series, then G(x) = exp(Σ_{n≥1} G(L(n) x)^n x^n/n)
is an integer series.

Definitions.
* `bf L g m = m * [x^m] Σ_{n=1}^{m} G(L(n) x)^n x^n / n` with G = Σ_{i<m} g(i) x^i (the
  coefficients of G of degree ≥ m do not reach x^m since n ≥ 1). `G(L(n) x)` is the polynomial
  composition `G.comp (C (L n) * X)`.
* `a L = recSeq (bf L)`: a(0) = 1, (N+1) a(N+1) = Σ_{j=0..N} bf a (j+1) a(N-j), i.e. the
  coefficients of exp(S) where x S' has coefficients `bf a m` (the functional equation).
* `sig n = Σ_{d | n} d` (σ(n)); `A163921 = a sig`.

Main theorems.
* `A163921_general (L) (hL : Gauss congruences of L at every prime) n : ∃ z : ℤ, a L n = z`.
* `A163921_conjecture (L) (hF : ∀ n, ∃ z : ℤ, expCoeff L n = z) n : ∃ z : ℤ, a L n = z`: the
  conjecture as stated (hypothesis: exp(Σ L(n) x^n/n) is an integer series).
* `A163921_int n : ∃ z : ℤ, a sig n = z`: the entry's own series.

Route: library `OpenProblemsLib.DworkEuler`. For integer g below degree N, bf g m (m ≤ N) is the
row sum `rowB F 0 W m` with F = x G_N and W(m, n) = L(n)^(m-n) (`coeff_comp_C_mul_X`,
`coeff_X_mul_gpoly_pow`); W satisfies the ray congruences by `W1_pow` (κ(m,n) = m - n), so
`rowB_gauss` gives Gauss congruences and `recSeq_int` integrality. The hypothesis on L enters
through `gauss_of_expCoeff_int` (integral exp ⇒ Gauss congruences) and, for σ, `LGp_of_euler`.
Not checked here: that the recurrence is the OEIS "exp(...)" (standard reading); data agreement
(certificate/check.py).
-/

namespace A163921

open Polynomial OpenProblemsLib.Dwork OpenProblemsLib.DworkEuler

/-- `m * [x^m] Σ_{n=1}^{m} G(L(n) x)^n x^n / n` with `G = Σ_{i<m} g i x^i`. -/
noncomputable def bf (L : ℕ → ℤ) (g : ℕ → ℚ) (m : ℕ) : ℚ :=
  (m : ℚ) * ∑ n ∈ Finset.Icc 1 m,
    ((((gpoly g m).comp (C (L n : ℚ) * X)) ^ n * X ^ n).coeff m) / (n : ℚ)

/-- Coefficients of G(x) = exp(Σ_{n≥1} G(L(n) x)^n x^n/n). -/
noncomputable def a (L : ℕ → ℤ) : ℕ → ℚ := recSeq (bf L)

/-- σ(n) = Σ_{d ∣ n} d. -/
def sig (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d : ℤ)

theorem bf_local (L : ℕ → ℤ) : Local (bf L) := by
  intro g g' m h
  have : gpoly g m = gpoly g' m :=
    Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])
  simp only [bf, this]

theorem bf_eq_rowB (L : ℕ → ℤ) (gz : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N) :
    bf L (fun i => (gz i : ℚ)) m =
      (rowB ((X * gpoly gz N).map C) (fun _ => 0) (fun m n => L n ^ (m - n)) m : ℚ) := by
  rw [rowB_eq_Icc, bf, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  rw [V_cast_map, coeff_X_mul_gpoly_pow gz N m n hm hn.2, coeff_mul_X_pow', ← pow_comp,
    coeff_comp_C_mul_X]
  simp only [hn.2, ↓reduceIte]
  ring

theorem A163921_general (L : ℕ → ℤ) (hL : ∀ p : ℕ, p.Prime → LGp p L) (n : ℕ) :
    ∃ z : ℤ, a L n = z := by
  apply recSeq_int (bf L) (bf_local L)
  intro gz N
  refine ⟨rowB ((X * gpoly gz N).map C) (fun _ => 0) (fun m n => L n ^ (m - n)), ?_, ?_⟩
  · intro p hp
    apply rowB_gauss _ _ ycond_zero _ p hp
    exact W1_pow p hp L (hL p hp) (fun m n => m - n) (fun m n => (Nat.mul_sub p m n).symm)
      (fun k m n hm hn => Nat.dvd_sub hm hn)
  · intro m _ hm
    exact bf_eq_rowB L gz N m hm

/-- The conjecture of A163921 as stated: if exp(Σ L(n) x^n/n) is an integer series, so is G. -/
theorem A163921_conjecture (L : ℕ → ℤ) (hF : ∀ n, ∃ z : ℤ, expCoeff L n = z) (n : ℕ) :
    ∃ z : ℤ, a L n = z :=
  A163921_general L (fun p hp => gauss_of_expCoeff_int L hF p hp) n

/-- A163921 itself (L = σ). -/
theorem A163921_int (n : ℕ) : ∃ z : ℤ, a sig n = z :=
  A163921_general sig (fun p hp => LGp_of_euler sig (fun _ => 1)
    (fun n _ => by simp [sig]) p hp) n
