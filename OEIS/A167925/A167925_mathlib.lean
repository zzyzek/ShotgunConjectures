/-
OEIS A167925. Name (since Greubel, 2023): T(n, k) = sqrt(k+1)^(n-1) * ChebyshevU(n-1, sqrt(k+1)/2),
read by rows 0 <= k <= n. Old comment (Daddi 2011): "Conjecture: a(6),...,a(9) = coefficient of
x^2 in the Maclaurin expansion of 1/(n*x^2+n*x+1) for n=1..4; a(10..14) = -coefficient of x^3
...". Greubel turned it into the formula T(n, k) = (-1)^(n+1) [x^(n-1)] 1/(1 + (k+1)x + (k+1)x^2).

  * `A167925_V a`: V 0 = 1, V 1 = a, V (m+2) = a V (m+1) - a V m (integers).
  * `A167925_cheb`: sqrt(a)^m * U_m(sqrt(a)/2) = V a m for real a >= 0 (Mathlib Chebyshev U).
  * `A167925_series`: (1 + aX + aX^2) * Σ (-1)^m V a m X^m = 1, so the Maclaurin coefficient of
    x^m in 1/(1 + aX + aX^2) is (-1)^m V a m.
  * `A167925_main`: for n >= 1 the two closed forms agree: with a = k + 1,
    sqrt(a)^(n-1) U_{n-1}(sqrt(a)/2) = (-1)^(n+1) * [x^(n-1)] of that series.
  * `A167925_data`: the 55 data terms (rows n = 0..9) equal T(n, k) (row 0 is 0).
Checked: all of the above. Not checked: the row n = 0 convention of the Chebyshev form
(U_{-1} = 0, so T(0, 0) = 0, matching the data).
-/
import Mathlib

open Polynomial

def A167925_V (a : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a
  | m + 2 => a * A167925_V a (m + 1) - a * A167925_V a m

/-- T(n, k) from the recurrence; row 0 is 0. -/
def A167925_T (n k : ℕ) : ℤ := if n = 0 then 0 else A167925_V (k + 1) (n - 1)

theorem A167925_cheb (a : ℝ) (ha : 0 ≤ a) (b : ℤ) (hb : (b : ℝ) = a) (m : ℕ) :
    Real.sqrt a ^ m * (Chebyshev.U ℝ (m : ℤ)).eval (Real.sqrt a / 2) = A167925_V b m := by
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  suffices H : ∀ m : ℕ,
      Real.sqrt a ^ m * (Chebyshev.U ℝ (m : ℤ)).eval (Real.sqrt a / 2) = A167925_V b m ∧
      Real.sqrt a ^ (m + 1) * (Chebyshev.U ℝ ((m + 1 : ℕ) : ℤ)).eval (Real.sqrt a / 2) =
        A167925_V b (m + 1) from (H m).1
  intro m
  induction m with
  | zero =>
    refine ⟨by simp [A167925_V], ?_⟩
    simp [A167925_V, Chebyshev.U_one, hb]
    nlinarith [hs]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have e : ((m + 1 + 1 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
    rw [e, Chebyshev.U_add_two]
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat]
    have h1 := ih.1
    have h2 := ih.2
    push_cast at h2
    show _ = ((b * A167925_V b (m + 1) - b * A167925_V b m : ℤ) : ℝ)
    push_cast
    rw [hb, ← h1, ← h2]
    linear_combination (Real.sqrt a ^ m * (Real.sqrt a *
      (Chebyshev.U ℝ ((m : ℤ) + 1)).eval (Real.sqrt a / 2) -
      (Chebyshev.U ℝ (m : ℤ)).eval (Real.sqrt a / 2))) * hs

theorem A167925_series (a : ℤ) :
    (1 + PowerSeries.C (a : ℚ) * PowerSeries.X + PowerSeries.C (a : ℚ) * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun m => ((-1) ^ m * A167925_V a m : ℚ)) = 1 := by
  ext m
  rcases m with _ | _ | m
  · simp [A167925_V]
  · simp [add_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, pow_two, A167925_V]
  · simp [add_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, A167925_V, pow_succ]
    ring

theorem A167925_main (n k : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((k : ℝ) + 1) ^ (n - 1) *
        (Chebyshev.U ℝ ((n - 1 : ℕ) : ℤ)).eval (Real.sqrt ((k : ℝ) + 1) / 2) =
      (((-1) ^ (n + 1) *
        PowerSeries.coeff (n - 1) (PowerSeries.mk (fun m => ((-1) ^ m * A167925_V (k + 1) m : ℚ)))
          : ℚ) : ℝ) ∧
      A167925_T n k = A167925_V (k + 1) (n - 1) := by
  refine ⟨?_, by unfold A167925_T; simp [show n ≠ 0 by omega]⟩
  rw [A167925_cheb ((k : ℝ) + 1) (by positivity) (k + 1) (by push_cast; ring)]
  rw [PowerSeries.coeff_mk]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [← mul_assoc, ← pow_add, show j + 1 + 1 + j = 2 * (j + 1) by ring, pow_mul]
  norm_num

theorem A167925_data :
    ((List.range 10).flatMap fun n => (List.range (n + 1)).map fun k => A167925_T n k) =
      [0, 1, 1, 1, 2, 3, 0, 2, 6, 12, -1, 0, 9, 32, 75, -1, -4, 9, 80, 275, 684, 0, -8, 0, 192,
       1000, 3240, 8232, 1, -8, -27, 448, 3625, 15336, 47677, 122368, 1, 0, -81, 1024, 13125,
       72576, 276115, 835584, 2158569, 0, 16, -162, 2304, 47500, 343440, 1599066, 5705728,
       16953624, 44010000] := by
  decide
