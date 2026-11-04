/-
OEIS A192205, Mathlib proof.

a(n) = sum of the absolute values of the coefficients of (1 - x - x^2 + x^3)^n
(an integer polynomial, `Polynomial ℤ`).

Main theorem `A192205_main`: a(n)^(1/n) → 16√3/9 as n → ∞ (README result).

Proof: let M = 16√3/9, so M^2 = 256/27 = max over |z| = 1 of
|1 - z - z^2 + z^3|^2 = 8 (1 - Re z)^2 (1 + Re z).
- Lower bound: at z0 = -1/3 + (2√2/3) i, |P(z0)^n| = M^n ≤ a(n) (triangle
  inequality on the unit circle).
- Upper bound: Parseval (Mathlib `Polynomial.sum_sq_norm_coeff_eq_circleAverage`)
  gives sum c_k^2 ≤ M^(2n), and Cauchy–Schwarz over the ≤ 3n + 1 coefficients
  gives a(n) ≤ √(3n + 1) M^n ≤ 2n M^n.
Then M ≤ a(n)^(1/n) ≤ (2n)^(1/n) M and (2n)^(1/n) → 1.

Not checked: nothing (the entry's side remark sum c_k^2 = C(4n, n) is not
used and not checked).
-/
import Mathlib

open Polynomial Filter Topology

/-- The polynomial 1 - x - x^2 + x^3 over ℤ. -/
noncomputable def A192205_P : ℤ[X] := 1 - X - X ^ 2 + X ^ 3

/-- a(n) = sum of |coefficients| of P^n. -/
noncomputable def A192205_a (n : ℕ) : ℤ :=
  ∑ k ∈ (A192205_P ^ n).support, |(A192205_P ^ n).coeff k|

theorem A192205_norm_sq (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(A192205_P.map (Int.castRingHom ℂ)).eval z‖ ^ 2 = 8 * (1 - z.re) ^ 2 * (1 + z.re) := by
  have hev : (A192205_P.map (Int.castRingHom ℂ)).eval z = (1 - z) ^ 2 * (1 + z) := by
    simp [A192205_P]
    ring
  have hz2 : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    linarith
  have h1 : ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith
  have h2 : ‖1 + z‖ ^ 2 = 2 + 2 * z.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith
  rw [hev, norm_mul, norm_pow, mul_pow, ← pow_mul, show 2 * 2 = 2 * 2 from rfl, pow_mul, h1, h2]
  ring

theorem A192205_le (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(A192205_P.map (Int.castRingHom ℂ)).eval z‖ ^ 2 ≤ 256 / 27 := by
  rw [A192205_norm_sq z hz]
  have h1 : z.re ≤ 1 := by
    have := Complex.re_le_norm z
    linarith
  nlinarith [mul_nonneg (sq_nonneg (z.re + 1 / 3)) (show (0 : ℝ) ≤ 5 / 3 - z.re by linarith)]

theorem A192205_main :
    Tendsto (fun n : ℕ => ((A192205_a n : ℤ) : ℝ) ^ (1 / (n : ℝ))) atTop
      (𝓝 (16 * Real.sqrt 3 / 9)) := by
  set M : ℝ := 16 * Real.sqrt 3 / 9 with hM
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hM0 : 0 < M := by positivity
  have hM2 : M ^ 2 = 256 / 27 := by rw [hM]; nlinarith
  set Pc := A192205_P.map (Int.castRingHom ℂ) with hPc
  -- Coefficients of the complex polynomial Pc^n.
  --
  have hq : ∀ n, (A192205_P ^ n).map (Int.castRingHom ℂ) = Pc ^ n := fun n => by
    rw [Polynomial.map_pow]
  have hsupp : ∀ n, ((A192205_P ^ n).map (Int.castRingHom ℂ)).support = (A192205_P ^ n).support :=
    fun n => support_map_of_injective _ (RingHom.injective_int _)
  have hcoef : ∀ n k, ‖((A192205_P ^ n).map (Int.castRingHom ℂ)).coeff k‖ =
      |((A192205_P ^ n).coeff k : ℝ)| := by
    intro n k
    rw [coeff_map]
    simp [Complex.norm_intCast]
  have ha : ∀ n : ℕ, ((A192205_a n : ℤ) : ℝ) = ∑ k ∈ (A192205_P ^ n).support,
      ‖((A192205_P ^ n).map (Int.castRingHom ℂ)).coeff k‖ := by
    intro n
    simp only [hcoef, A192205_a]
    push_cast
    rfl
  -- Lower bound M^n ≤ a(n).
  --
  set z0 : ℂ := ⟨-1 / 3, 2 * Real.sqrt 2 / 3⟩ with hz0
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz0n : ‖z0‖ = 1 := by
    have : ‖z0‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hz0]
      simp only
      nlinarith
    have h0 : 0 ≤ ‖z0‖ := norm_nonneg _
    nlinarith
  have hPz0 : ‖Pc.eval z0‖ = M := by
    have h := A192205_norm_sq z0 hz0n
    rw [← hPc, hz0] at h
    simp only at h
    have : ‖Pc.eval z0‖ ^ 2 = M ^ 2 := by rw [h, hM2]; norm_num
    have h0 : 0 ≤ ‖Pc.eval z0‖ := norm_nonneg _
    nlinarith
  have hlow : ∀ n : ℕ, M ^ n ≤ ((A192205_a n : ℤ) : ℝ) := by
    intro n
    rw [ha, ← hPz0, ← norm_pow, ← eval_pow, ← hq, eval_eq_sum, Polynomial.sum_def, hsupp]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [norm_mul, norm_pow, hz0n, one_pow, mul_one]
  -- Upper bound a(n) ≤ 2 n M^n for n ≥ 1.
  --
  have hl2 : ∀ n : ℕ, ∑ k ∈ (A192205_P ^ n).support,
      ‖((A192205_P ^ n).map (Int.castRingHom ℂ)).coeff k‖ ^ 2 ≤ (M ^ n) ^ 2 := by
    intro n
    rw [← hsupp, Polynomial.sum_sq_norm_coeff_eq_circleAverage]
    apply Real.circleAverage_mono_on_of_le_circle
    · apply ContinuousOn.circleIntegrable'
      fun_prop
    · intro z hz
      simp only [Metric.mem_sphere, dist_zero_right, abs_one] at hz
      have hle : ‖Pc.eval z‖ ≤ M := by
        have h := A192205_le z hz
        rw [← hPc, ← hM2] at h
        nlinarith [norm_nonneg (Pc.eval z)]
      rw [hq, eval_pow, norm_pow]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hle n) 2
  have hcard : ∀ n : ℕ, ((A192205_P ^ n).support.card : ℝ) ≤ 3 * n + 1 := by
    intro n
    have hdeg : (A192205_P ^ n).natDegree ≤ 3 * n := by
      refine natDegree_pow_le.trans ?_
      have : A192205_P.natDegree ≤ 3 := by
        unfold A192205_P
        compute_degree
      nlinarith
    have := Finset.card_le_card (supp_subset_range_natDegree_succ (p := A192205_P ^ n))
    rw [Finset.card_range] at this
    exact_mod_cast (show (A192205_P ^ n).support.card ≤ 3 * n + 1 by omega)
  have hup : ∀ n : ℕ, 1 ≤ n → ((A192205_a n : ℤ) : ℝ) ≤ 2 * n * M ^ n := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (A192205_P ^ n).support (fun _ => (1 : ℝ))
      (fun k => ‖((A192205_P ^ n).map (Int.castRingHom ℂ)).coeff k‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    rw [← ha] at hcs
    have hsq : ((A192205_a n : ℤ) : ℝ) ^ 2 ≤ (2 * n * M ^ n) ^ 2 := by
      calc _ ≤ _ := hcs
        _ ≤ (3 * n + 1) * (M ^ n) ^ 2 :=
          mul_le_mul (hcard n) (hl2 n) (Finset.sum_nonneg (fun _ _ => by positivity))
            (by positivity)
        _ ≤ (2 * n) ^ 2 * (M ^ n) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
        _ = _ := by ring
    have h0 : 0 ≤ ((A192205_a n : ℤ) : ℝ) := le_trans (by positivity) (hlow n)
    have hb : 0 ≤ 2 * (n : ℝ) * M ^ n := by positivity
    nlinarith
  -- Squeeze.
  --
  have hroot : ∀ n : ℕ, 1 ≤ n → (M ^ n) ^ (1 / (n : ℝ)) = M := by
    intro n hn
    rw [one_div]
    exact Real.pow_rpow_inv_natCast hM0.le (by omega)
  have h2n : Tendsto (fun n : ℕ => (2 * (n : ℝ)) ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (2 * (n : ℝ)) ^ (1 / (2 * (n : ℝ)))) atTop (𝓝 1) :=
      tendsto_rpow_div.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    have h2 := h1.pow 2
    rw [one_pow] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
    norm_num
  have hupper : Tendsto (fun n : ℕ => (2 * (n : ℝ)) ^ (1 / (n : ℝ)) * M) atTop (𝓝 M) := by
    simpa using h2n.mul_const M
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← hroot n hn]
    exact Real.rpow_le_rpow (by positivity) (hlow n) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 : 0 ≤ ((A192205_a n : ℤ) : ℝ) := le_trans (by positivity) (hlow n)
    calc ((A192205_a n : ℤ) : ℝ) ^ (1 / (n : ℝ)) ≤ (2 * n * M ^ n) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow h0 (hup n hn) (by positivity)
      _ = (2 * (n : ℝ)) ^ (1 / (n : ℝ)) * (M ^ n) ^ (1 / (n : ℝ)) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = _ := by rw [hroot n hn]
