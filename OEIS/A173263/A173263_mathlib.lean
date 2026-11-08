/-
OEIS A173263, Mathlib proof.

A173263: numbers n such that ChebyshevT(n/2, n) is not an integer. For real ν and
x >= 1, ChebyshevT(ν, x) = cos(ν arccos x) = cosh(ν arcosh x) (`chebT`, Mathlib
`Real.arcosh`); for integer ν this is the Chebyshev polynomial (`chebT_even`
uses Mathlib `Polynomial.Chebyshev.T_real_cosh`).

Old conjecture in the entry: the sequence is finite and complete (data ended at 87).

Main theorem `A173263_main`: for n >= 1, ChebyshevT(n/2, n) is not an integer iff
n is odd and (n+1)/2 is not a perfect square.
`A173263_infinite`: the set of such n is infinite (it contains 2(k+1)^2 + 1 for
every k), so the conjecture is false.

Method (Israel): for n = 2m+1 put y = sqrt(m+1) and θ = arcosh y; then
arcosh n = 2θ and ChebyshevT(n/2, n) = T_n(y) = y * w with w an integer
(odd Chebyshev polynomials are x times a polynomial in x^2), and w != 0
since cosh >= 1; y is irrational unless m+1 is a square.

Outside Lean: none (reading ChebyshevT of non-integer degree as cosh(ν arcosh x)
for x >= 1, the standard analytic continuation used by Mathematica, is the
definition).
-/
import Mathlib

open Real Polynomial

namespace A173263

/-- `ChebyshevT(ν, x) = cosh(ν arcosh x)` for real `ν` and `x >= 1`. -/
noncomputable def chebT (ν x : ℝ) : ℝ := Real.cosh (ν * Real.arcosh x)

lemma T_int (k : ℕ) (x : ℤ) : ∃ z : ℤ, (Chebyshev.T ℝ (k : ℤ)).eval (x : ℝ) = z := by
  refine ⟨(Chebyshev.T ℤ (k : ℤ)).eval x, ?_⟩
  rw [← Chebyshev.map_T (Int.castRingHom ℝ), eval_intCast_map]
  simp

/-- With `y^2 = N` an integer, `T_{2j}(y)` is an integer and `T_{2j+1}(y)` is `y` times one. -/
lemma T_parity (N : ℕ) (y : ℝ) (hy : y ^ 2 = N) (j : ℕ) :
    (∃ z : ℤ, (Chebyshev.T ℝ ((2 * j : ℕ) : ℤ)).eval y = z) ∧
    (∃ w : ℤ, (Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval y = y * w) := by
  induction j with
  | zero => exact ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩
  | succ j ih =>
    obtain ⟨⟨z, hz⟩, ⟨w, hw⟩⟩ := ih
    have e1 : ((2 * (j + 1) : ℕ) : ℤ) = ((2 * j : ℕ) : ℤ) + 2 := by push_cast; ring
    have e1' : ((2 * j : ℕ) : ℤ) + 1 = ((2 * j + 1 : ℕ) : ℤ) := by push_cast; ring
    have h2 : (Chebyshev.T ℝ ((2 * (j + 1) : ℕ) : ℤ)).eval y = 2 * N * w - z := by
      rw [e1, Chebyshev.T_add_two, e1']
      simp only [eval_sub, eval_mul, eval_X, eval_ofNat, hz, hw]
      rw [← hy]; ring
    refine ⟨⟨2 * N * w - z, by rw [h2]; push_cast; ring⟩, ⟨2 * (2 * N * w - z) - w, ?_⟩⟩
    have e2 : ((2 * (j + 1) + 1 : ℕ) : ℤ) = ((2 * j + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
    have e2' : ((2 * j + 1 : ℕ) : ℤ) + 1 = ((2 * (j + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [e2, Chebyshev.T_add_two, e2']
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat, h2, hw]
    push_cast
    ring

/-- Even `n = 2m`: `ChebyshevT(m, 2m)` is the integer `T_m(2m)`. -/
lemma chebT_even (m : ℕ) (hm : 1 ≤ m) :
    ∃ z : ℤ, chebT (((2 * m : ℕ) : ℝ) / 2) ((2 * m : ℕ) : ℝ) = z := by
  have hx : (1 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * m)
  have h := Chebyshev.T_real_cosh (Real.arcosh ((2 * m : ℕ) : ℝ)) (m : ℤ)
  rw [cosh_arcosh hx] at h
  obtain ⟨z, hz⟩ := T_int m (2 * m : ℕ)
  refine ⟨z, ?_⟩
  rw [chebT, show (((2 * m : ℕ) : ℝ) / 2) = ((m : ℤ) : ℝ) by push_cast; ring, ← h]
  exact_mod_cast hz

/-- Odd `n = 2m+1`: `ChebyshevT(n/2, n) = sqrt(m+1) * w` with `w` an integer. -/
lemma chebT_odd (m : ℕ) :
    ∃ w : ℤ, chebT (((2 * m + 1 : ℕ) : ℝ) / 2) ((2 * m + 1 : ℕ) : ℝ) = √((m : ℝ) + 1) * w := by
  set y := √((m : ℝ) + 1) with hydef
  have hy2 : y ^ 2 = ((m + 1 : ℕ) : ℝ) := by
    rw [hydef, sq_sqrt (by positivity)]; push_cast; ring
  have hy1 : 1 ≤ y := by
    rw [hydef]; exact Real.one_le_sqrt.2 (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)
  set θ := Real.arcosh y with hθ
  have hc : Real.cosh θ = y := cosh_arcosh hy1
  have hθ0 : 0 ≤ θ := arcosh_nonneg hy1
  have h2 : Real.cosh (2 * θ) = ((2 * m + 1 : ℕ) : ℝ) := by
    rw [Real.cosh_two_mul, Real.sinh_sq, hc]
    push_cast at hy2 ⊢
    nlinarith [hy2]
  have harc : Real.arcosh ((2 * m + 1 : ℕ) : ℝ) = 2 * θ := by
    rw [← h2, arcosh_cosh (by linarith)]
  obtain ⟨w, hw⟩ := (T_parity (m + 1) y hy2 m).2
  refine ⟨w, ?_⟩
  have h := Chebyshev.T_real_cosh θ ((2 * m + 1 : ℕ) : ℤ)
  rw [hc, hw] at h
  rw [chebT, harc, show ((2 * m + 1 : ℕ) : ℝ) / 2 * (2 * θ) = (((2 * m + 1 : ℕ) : ℤ) : ℝ) * θ by
    push_cast; ring, ← h]

/-- Main theorem: for `n >= 1`, `ChebyshevT(n/2, n)` is not an integer iff `n` is odd and
`(n+1)/2` is not a square. -/
theorem A173263_main (n : ℕ) (hn : 1 ≤ n) :
    (¬ ∃ z : ℤ, chebT ((n : ℝ) / 2) n = z) ↔ (Odd n ∧ ¬ IsSquare ((n + 1) / 2)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := chebT_even m (by omega)
    constructor
    · intro h'; exact absurd h h'
    · rintro ⟨ho, _⟩
      exact absurd ho (Nat.not_odd_iff_even.2 (even_two_mul m))
  · obtain ⟨w, hw⟩ := chebT_odd m
    rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega]
    constructor
    · intro h
      refine ⟨odd_two_mul_add_one m, ?_⟩
      rintro ⟨r, hr⟩
      apply h
      refine ⟨r * w, ?_⟩
      rw [hw, show ((m : ℝ) + 1) = (r : ℝ) ^ 2 by exact_mod_cast (by rw [hr]; ring),
        sqrt_sq (by positivity)]
      push_cast; ring
    · rintro ⟨_, hsq⟩ ⟨z, hz⟩
      have hirr : Irrational (√((m : ℝ) + 1)) := by
        have := irrational_sqrt_natCast_iff.2 hsq
        exact_mod_cast this
      have hw0 : w ≠ 0 := by
        rintro rfl
        have h1 := Real.one_le_cosh ((((2 * m + 1 : ℕ) : ℝ) / 2) * Real.arcosh ((2 * m + 1 : ℕ) : ℝ))
        rw [← chebT, hw] at h1
        simp at h1
        linarith
      apply Int.not_irrational z
      rw [← hz, hw]
      exact hirr.mul_intCast hw0

/-- The sequence is infinite: it contains `2(k+1)^2 + 1` for every `k`. -/
theorem A173263_infinite : {n : ℕ | 1 ≤ n ∧ ¬ ∃ z : ℤ, chebT ((n : ℝ) / 2) n = z}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 * (k + 1) ^ 2 + 1)
  · intro a b h
    simp only at h
    have : (a + 1) ^ 2 = (b + 1) ^ 2 := by omega
    have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) this
    omega
  · intro k
    refine ⟨by omega, (A173263_main _ (by omega)).2 ⟨⟨(k + 1) ^ 2, by ring⟩, ?_⟩⟩
    rw [show (2 * (k + 1) ^ 2 + 1 + 1) / 2 = (k + 1) ^ 2 + 1 by omega]
    rintro ⟨r, hr⟩
    have h1 : k + 1 < r := by nlinarith
    have h2 : r < k + 2 := by nlinarith
    omega
