import Mathlib
import OpenProblemsLib.Pratt

/-!
# Short-interval primes: a prime in `(x, 1.21 x]` for every real `x ≥ 25`

Chebyshev's 1852 method gives `ψ(x) ≥ a x - O(log x)` and `ψ(x) ≤ (6/5) a x + O(log² x)` with
`a = (7/15) log 2 + (3/10) log 3 + (1/6) log 5 = 0.92129…`. Because `1.21 a > (6/5) a`, the
difference `θ(1.21 x) - θ(x)` is positive for `x ≥ 10^8`; below that a chain of 85 primes
`29, 31, 37, …, 118074017` (each at most `1.21` times the previous one, primality by Pratt
certificates checked in the kernel) covers every `x ∈ [25, 10^8)`.

Main results.
* `psi_lower` : `ψ x ≥ a x - 5 log x + 5` for `x ≥ 30` (Chebyshev).
* `psi_upper` : `ψ x ≤ (6/5) a x + (log x / log 6)(5 log x - 5) + 170` for `x ≥ 30`.
* `exists_prime_of_theta_lt` : `θ x < θ y` gives a prime in `(x, y]`.
* `exists_prime_Ioc_large` : a prime in `(x, 1.21 x]` for real `x ≥ 10^8`.
* `exists_prime_Ioc_mul` : a prime in `(x, 1.21 x]` for real `x ≥ 25`.
* `exists_prime_Ioc_mul_nat` : for `n ≥ 25` a prime `p` with `n < p` and `100 p ≤ 121 n`.

Checked: everything above, axioms propext, Classical.choice, Quot.sound.

Attribution. The definitions `T`, `E`, `ν`, `U`, `a`, `e` and the lemmas from `T.le` through
`psi_diff_upper` are adapted from PrimeNumberTheoremAnd, file
`PrimeNumberTheoremAnd/IEANTN/Chebyshev.lean` (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
copyright the PrimeNumberTheoremAnd contributors, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0). Changes: blueprint attributes removed, the
LeanCert interval tables for `log 2`, `log 3`, `log 5`, `log 30` replaced by Mathlib's
`Real.log_two_gt_d9` and its relatives, everything placed in namespace
`OpenProblemsLib.ShortIntervalPrimes`. `psi_upper` and everything after it are new.
-/

namespace OpenProblemsLib.ShortIntervalPrimes

open Real Finsupp Finset Chebyshev
open ArithmeticFunction hiding log

attribute [local fun_prop] DifferentiableAt.differentiableWithinAt

lemma log_2_gt : 0.693147 < log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
lemma log_2_lt : log 2 < 0.693148 := lt_trans Real.log_two_lt_d9 (by norm_num)
lemma log_3_gt : 1.098612 < log 3 := lt_trans (by norm_num) Real.log_three_gt_d9
lemma log_3_lt : log 3 < 1.098613 := lt_trans Real.log_three_lt_d9 (by norm_num)
lemma log_5_gt : 1.609437 < log 5 := lt_trans (by norm_num) Real.log_five_gt_d9
lemma log_5_lt : log 5 < 1.609438 := lt_trans Real.log_five_lt_d9 (by norm_num)

lemma log_30_gt : 3.401197 < log 30 := by
  have h : log 30 = log 2 + log 3 + log 5 := by
    rw [← log_mul (by norm_num) (by norm_num), ← log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [h]; linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

/-- Adapted from PrimeNumberTheoremAnd (`ZetaBounds.lean`). -/
lemma Ioc_eq_Icc (M N : ℕ) : Finset.Ioc N M = Finset.Icc (N + 1) M := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Icc]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    sum_insert right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have h3 : ∀ t ∈ interior (Set.Ici 1), DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    fun_prop ( disch := positivity )
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop ( disch := positivity )
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by fun_prop
  have h2 : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) h5 h3 h4
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    exact h2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Ico_insert_right hone_le_floor, sum_insert right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have h1 : ∀ n ≥ 1, ∑ i ∈ Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Ico 1 n, log i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => grind [Nat.Ico_succ_right_eq_insert_Ico]
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) = log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i := by
    exact h1 ⌊x⌋₊ hone_le_floor
  have int_le_T : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [mono_log.integral_le_sum_Ico hone_le_floor]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x := (intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith) intervalIntegral.intervalIntegrable_log'
            intervalIntegrable_const fun t ht ↦ log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2)
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith)|>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [mem_sdiff, mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

/-- The support of `ν` is `{1, 2, 3, 5, 30}`. Used whenever we need to unfold `ν.sum`. -/
private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]; grind

/-- Unfold `ν.sum (fun m w ↦ w * f m)` into its five-term expansion.
This avoids repeating the `sum_add_index` / `sum_sub_index` chain every time
we need to compute a `ν`-weighted sum. -/
private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

/-- Unfold `E ν y` into an explicit expression in terms of floors of `y / k`.
This is the key formula repeatedly used to analyse `E ν`. -/
private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

/-- The classical sandwich `k * ⌊y/k⌋₊ ≤ ⌊y⌋₊ < k * ⌊y/k⌋₊ + k` for `k ≥ 1` and `y ≥ 0`. -/
private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  norm_num [ν, add_div, sum_add_index', sub_div, sum_sub_index]

theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + (30 / k) := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero, add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 := by omega
    have hlb' : ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hlb
    have hub' : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_) (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1

noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by
  norm_num [a_simpl]
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9,
    Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]

noncomputable def e (x : ℝ) : ℝ :=
  (T x - (x * log x - x + 1))

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + (e x) := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * (log (x / m))))
          - ν.sum (fun m w ↦ w * (x / m))
          + ν.sum (fun _m w ↦ w)
          + ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]; rw [ν_sum_mul (fun m ↦ log m / m)]; push_cast; rfl
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]; push_cast; ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ)); simp at this; linarith

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 :=
    by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]; ring_nf; rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤ ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr; exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]; ring
  rw [hlog_split]
  -- Once the support of `ν` is known explicitly, both `habs` and `hsum_eq`
  -- reduce to concrete arithmetic over a five-element finset.
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1:ℕ) ∉ ({2,3,5,30} : Finset ℕ)),
               sum_insert (by decide : (2:ℕ) ∉ ({3,5,30} : Finset ℕ)),
               sum_insert (by decide : (3:ℕ) ∉ ({5,30} : Finset ℕ)),
               sum_insert (by decide : (5:ℕ) ∉ ({30} : Finset ℕ)),
               sum_singleton, ν, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]; norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) = log 2 + log 3 + log 5 + log 30 := by
      rw [expand_sum _ (by intros; simp)]
      simp [log_one]
    linarith [log_2_gt, log_3_gt, log_5_gt, log_30_gt]
  grw [hgeq6]; rw [habs]; linarith

theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_ge_weighted x (by linarith), h2.1]

theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_diff_le_weighted x (by linarith), h2.2]

-- Proof splits into many cases

/-! ## Upper bound for `ψ` by telescoping (new) -/

/-- Crude bound for `ψ` below 30, from Mathlib's `psi_le_const_mul_self`. -/
lemma psi_small (y : ℝ) (hy0 : 0 ≤ y) (hy : y < 30) : ψ y ≤ 170 := by
  have h := psi_le_const_mul_self hy0
  have h4 : log 4 < 1.4 := by
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [log_2_lt]
  nlinarith [mul_le_mul_of_nonneg_right h4.le hy0]

lemma geom_six (x : ℝ) (n : ℕ) : ∑ i ∈ range n, x / 6 ^ i = 6 / 5 * x * (1 - 1 / 6 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    field_simp
    ring

lemma psi_tele (x : ℝ) (hx : 0 < x) : ∀ n : ℕ, (∀ i < n, 30 ≤ x / 6 ^ i) →
    ψ x ≤ ψ (x / 6 ^ n) + ∑ i ∈ range n, (a * (x / 6 ^ i) + (5 * log x - 5)) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have hn : 30 ≤ x / 6 ^ n := h n (by omega)
    have h2 := psi_diff_upper (x / 6 ^ n) hn
    have h3 : x / 6 ^ n / 6 = x / 6 ^ (n + 1) := by rw [pow_succ, div_div]
    rw [h3] at h2
    have h4 : log (x / 6 ^ n) ≤ log x := by
      apply log_le_log (by positivity)
      exact div_le_self hx.le (one_le_pow₀ (by norm_num))
    rw [sum_range_succ]
    linarith

/-- Chebyshev's upper bound: `ψ x ≤ (6/5) a x + (log x / log 6)(5 log x - 5) + 170`
for `x ≥ 30`. -/
theorem psi_upper (x : ℝ) (hx : 30 ≤ x) :
    ψ x ≤ 6 / 5 * a * x + (log x / log 6) * (5 * log x - 5) + 170 := by
  have hx0 : 0 < x := by linarith
  have hex : ∃ n : ℕ, x / 6 ^ n < 30 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / 30) (by norm_num : (1 : ℝ) < 6)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by norm_num)] at hn
    linarith
  classical
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, x / 6 ^ n < 30 ∧ ∀ i < n, 30 ≤ x / 6 ^ i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_lt.mp (Nat.find_min hex hi)⟩
  have hn1 : n ≠ 0 := by
    intro h0
    rw [h0] at hn
    simp at hn
    linarith
  have h6n : (6 : ℝ) ^ n ≤ x := by
    have h := hmin (n - 1) (by omega)
    rw [le_div_iff₀ (by positivity)] at h
    have e : (6 : ℝ) ^ n = 6 ^ (n - 1) * 6 := by
      rw [← pow_succ]; congr 1; omega
    rw [e]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 6) (n - 1)]
  have hlog6 : 0 < log 6 := log_pos (by norm_num)
  have hnle : (n : ℝ) ≤ log x / log 6 := by
    rw [le_div_iff₀ hlog6, ← Real.log_pow]
    exact log_le_log (by positivity) h6n
  have hlogx : 1 ≤ log x := by
    have h30 : (1 : ℝ) < log 30 := by linarith [log_30_gt]
    linarith [log_le_log (by norm_num) hx]
  have ht := psi_tele x hx0 n hmin
  rw [sum_add_distrib, ← Finset.mul_sum, geom_six, sum_const, card_range, nsmul_eq_mul] at ht
  have ha : 0 ≤ a := le_trans (by norm_num) a_bound.1
  have hg : 0 ≤ a * (6 / 5 * x) * (1 / 6 ^ n) := by positivity
  have hm : (n : ℝ) * (5 * log x - 5) ≤ (log x / log 6) * (5 * log x - 5) :=
    mul_le_mul_of_nonneg_right hnle (by linarith)
  have hs := psi_small (x / 6 ^ n) (by positivity) hn
  nlinarith

/-! ## A prime in `(x, 1.21 x]` -/

/-- If `θ x < θ y` then some prime lies in `(x, y]`. -/
theorem exists_prime_of_theta_lt {x y : ℝ} (h : θ x < θ y) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra hne
  push Not at hne
  apply (not_le.mpr h)
  unfold theta
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [mem_filter, mem_Ioc] at hp ⊢
    obtain ⟨⟨hp0, hpy⟩, hpp⟩ := hp
    refine ⟨⟨hp0, ?_⟩, hpp⟩
    have hy : (p : ℝ) ≤ y := (Nat.le_floor_iff' hp0.ne').mp hpy
    have hpx : (p : ℝ) ≤ x := by
      by_contra hc
      push Not at hc
      linarith [hne p hpp hc]
    exact Nat.le_floor hpx
  · intro p _ _
    exact Real.log_natCast_nonneg p

/-- A prime in `(x, 1.21 x]` for every real `x ≥ 10^8`, from Chebyshev's bounds. -/
theorem exists_prime_Ioc_large (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ 1.21 * x := by
  apply exists_prime_of_theta_lt
  have hlow := psi_lower (1.21 * x) (by linarith)
  have hup := psi_upper x (by linarith)
  have hpt := psi_sub_theta_le (x := 1.21 * x) (by linarith)
  have htp := theta_le_psi x
  obtain ⟨ha1, _⟩ := a_bound
  have hs0 : 0 ≤ √x := sqrt_nonneg x
  have hss : √x * √x = x := mul_self_sqrt (by linarith)
  have hsr : √(1.21 * x) = 1.1 * √x := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1.21), show (1.21 : ℝ) = 1.1 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsr] at hpt
  have hs4 : 10 ^ 4 ≤ √x := by nlinarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, √x = 10 ^ 4 * u := ⟨√x / 10 ^ 4, by field_simp⟩
  have hu1 : 1 ≤ u := by nlinarith
  have hxu : x = 10 ^ 8 * u ^ 2 := by rw [← hss, hu]; ring
  have hlogs : log √x ≤ 9.2104 + u - 1 := by
    have h2 : log u ≤ u - 1 := log_le_sub_one_of_pos (by linarith)
    have h3 : log ((10 : ℝ) ^ 4) ≤ 9.2104 := by
      rw [Real.log_pow, show (10 : ℝ) = 2 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
      push_cast
      linarith [log_2_lt, log_5_lt]
    rw [hu, log_mul (by norm_num) (by linarith)]
    linarith
  have hlogx : log x = 2 * log √x := by
    have h := log_mul (x := √x) (y := √x) (by linarith) (by linarith)
    rw [hss] at h
    linarith
  have hL : log (1.21 * x) = log 1.21 + log x := log_mul (by norm_num) (by linarith)
  have h121 : log (1.21 : ℝ) ≤ 0.21 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.21); linarith
  have h121' : 0 ≤ log (1.21 : ℝ) := log_nonneg (by norm_num)
  have hlogx0 : 0 ≤ log x := log_nonneg (by linarith)
  have hLb : log (1.21 * x) ≤ 16.64 + 2 * u := by linarith
  have hL0 : 0 ≤ log (1.21 * x) := by linarith
  have hlogxL : log x ≤ log (1.21 * x) := by linarith
  have hlog6 : 1.79 ≤ log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
    linarith [log_2_gt, log_3_gt]
  have hq : (log x / log 6) * (5 * log x - 5) ≤ 2.8 * log (1.21 * x) ^ 2 := by
    have hd : log x / log 6 ≤ log x / 1.79 :=
      div_le_div_of_nonneg_left hlogx0 (by norm_num) hlog6
    have hd0 : 0 ≤ log x / log 6 := div_nonneg hlogx0 (by linarith)
    calc (log x / log 6) * (5 * log x - 5) ≤ (log x / log 6) * (5 * log x) :=
          mul_le_mul_of_nonneg_left (by linarith) hd0
      _ ≤ (log x / 1.79) * (5 * log x) := mul_le_mul_of_nonneg_right hd (by linarith)
      _ = (5 / 1.79) * (log x * log x) := by ring
      _ ≤ (5 / 1.79) * (log (1.21 * x) * log (1.21 * x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hlogxL hlogxL hlogx0 hL0) (by norm_num)
      _ ≤ 2.8 * log (1.21 * x) ^ 2 := by nlinarith [mul_nonneg hL0 hL0]
  have hsL : √x * log (1.21 * x) ≤ 10 ^ 4 * u * (16.64 + 2 * u) := by
    rw [hu]; exact mul_le_mul_of_nonneg_left hLb (by linarith)
  have hLL : log (1.21 * x) ^ 2 ≤ (16.64 + 2 * u) ^ 2 := pow_le_pow_left₀ hL0 hLb 2
  have hax : 0.0092 * x ≤ 0.01 * a * x := by nlinarith
  have huu : u ≤ u ^ 2 := by nlinarith
  nlinarith

/-! ## Small `x`: a chain of certified primes -/

/-- `chainOK (a :: l)`: the list increases and each entry is at most `1.21` times the previous. -/
def chainOK : List ℕ → Bool
  | a :: b :: l => decide (a < b) && decide (100 * b ≤ 121 * a) && chainOK (b :: l)
  | _ => true

theorem chainOK_cover : ∀ (l : List ℕ) (a : ℕ), chainOK (a :: l) = true →
    ∀ x : ℝ, (a : ℝ) ≤ x → (∃ p ∈ l, x < p) → ∃ p ∈ l, x < p ∧ 100 * (p : ℝ) ≤ 121 * x := by
  intro l
  induction l with
  | nil =>
    intro a _ x _ h
    obtain ⟨p, hp, _⟩ := h
    simp at hp
  | cons b l ih =>
    intro a hc x hax hex
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨_, hba⟩, hc⟩ := hc
    by_cases hxb : x < b
    · refine ⟨b, by simp, hxb, ?_⟩
      have : (100 * b : ℝ) ≤ 121 * a := by exact_mod_cast hba
      linarith
    · push Not at hxb
      obtain ⟨p, hp, hxp⟩ := hex
      rcases List.mem_cons.mp hp with rfl | hp'
      · linarith
      · obtain ⟨q, hq, h⟩ := ih b hc x hxb ⟨p, hp', hxp⟩
        exact ⟨q, List.mem_cons_of_mem _ hq, h⟩

/-- 85 primes from 29 to 118074017, each at most `1.21` times the previous. -/
def primeChain : List ℕ :=
  [29, 31, 37, 43, 47, 53, 61, 73, 83, 97, 113, 131, 157, 181, 211, 251, 293, 353, 421, 509,
   613, 739, 887, 1069, 1291, 1559, 1879, 2273, 2749, 3323, 4019, 4861, 5881, 7109, 8599, 10399,
   12577, 15217, 18401, 22259, 26927, 32579, 39419, 47681, 57689, 69779, 84431, 102161, 123601,
   149551, 180949, 218947, 264919, 320539, 387839, 469283, 567829, 687073, 831329, 1005883,
   1217113, 1472701, 1781939, 2156123, 2608897, 3156763, 3819671, 4621777, 5592343, 6766703,
   8187691, 9907099, 11987579, 14504951, 17550989, 21236693, 25696397, 31092629, 37622063,
   45522679, 55082437, 66649729, 80646161, 97581833, 118074017]

/-- Pratt certificate for every prime in `primeChain` (from `tools/pratt_cert.py`). -/
def primeChainCert : List PrattStep :=
  [⟨2, 1, []⟩,
    ⟨3, 2, [(2, 1)]⟩,
    ⟨7, 3, [(2, 1), (3, 1)]⟩,
    ⟨29, 2, [(2, 2), (7, 1)]⟩,
    ⟨5, 2, [(2, 2)]⟩,
    ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
    ⟨37, 2, [(2, 2), (3, 2)]⟩,
    ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩,
    ⟨11, 2, [(2, 1), (5, 1)]⟩,
    ⟨23, 5, [(2, 1), (11, 1)]⟩,
    ⟨47, 5, [(2, 1), (23, 1)]⟩,
    ⟨13, 2, [(2, 2), (3, 1)]⟩,
    ⟨53, 2, [(2, 2), (13, 1)]⟩,
    ⟨61, 2, [(2, 2), (3, 1), (5, 1)]⟩,
    ⟨73, 5, [(2, 3), (3, 2)]⟩,
    ⟨41, 6, [(2, 3), (5, 1)]⟩,
    ⟨83, 2, [(2, 1), (41, 1)]⟩,
    ⟨97, 5, [(2, 5), (3, 1)]⟩,
    ⟨113, 3, [(2, 4), (7, 1)]⟩,
    ⟨131, 2, [(2, 1), (5, 1), (13, 1)]⟩,
    ⟨157, 5, [(2, 2), (3, 1), (13, 1)]⟩,
    ⟨181, 2, [(2, 2), (3, 2), (5, 1)]⟩,
    ⟨211, 2, [(2, 1), (3, 1), (5, 1), (7, 1)]⟩,
    ⟨251, 6, [(2, 1), (5, 3)]⟩,
    ⟨293, 2, [(2, 2), (73, 1)]⟩,
    ⟨353, 3, [(2, 5), (11, 1)]⟩,
    ⟨421, 2, [(2, 2), (3, 1), (5, 1), (7, 1)]⟩,
    ⟨127, 3, [(2, 1), (3, 2), (7, 1)]⟩,
    ⟨509, 2, [(2, 2), (127, 1)]⟩,
    ⟨17, 3, [(2, 4)]⟩,
    ⟨613, 2, [(2, 2), (3, 2), (17, 1)]⟩,
    ⟨739, 3, [(2, 1), (3, 2), (41, 1)]⟩,
    ⟨443, 2, [(2, 1), (13, 1), (17, 1)]⟩,
    ⟨887, 5, [(2, 1), (443, 1)]⟩,
    ⟨89, 3, [(2, 3), (11, 1)]⟩,
    ⟨1069, 6, [(2, 2), (3, 1), (89, 1)]⟩,
    ⟨1291, 2, [(2, 1), (3, 1), (5, 1), (43, 1)]⟩,
    ⟨19, 2, [(2, 1), (3, 2)]⟩,
    ⟨1559, 19, [(2, 1), (19, 1), (41, 1)]⟩,
    ⟨313, 10, [(2, 3), (3, 1), (13, 1)]⟩,
    ⟨1879, 6, [(2, 1), (3, 1), (313, 1)]⟩,
    ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩,
    ⟨2273, 3, [(2, 5), (71, 1)]⟩,
    ⟨229, 6, [(2, 2), (3, 1), (19, 1)]⟩,
    ⟨2749, 6, [(2, 2), (3, 1), (229, 1)]⟩,
    ⟨151, 6, [(2, 1), (3, 1), (5, 2)]⟩,
    ⟨3323, 2, [(2, 1), (11, 1), (151, 1)]⟩,
    ⟨4019, 2, [(2, 1), (7, 2), (41, 1)]⟩,
    ⟨4861, 11, [(2, 2), (3, 5), (5, 1)]⟩,
    ⟨5881, 31, [(2, 3), (3, 1), (5, 1), (7, 2)]⟩,
    ⟨1777, 5, [(2, 4), (3, 1), (37, 1)]⟩,
    ⟨7109, 2, [(2, 2), (1777, 1)]⟩,
    ⟨179, 2, [(2, 1), (89, 1)]⟩,
    ⟨1433, 3, [(2, 3), (179, 1)]⟩,
    ⟨8599, 3, [(2, 1), (3, 1), (1433, 1)]⟩,
    ⟨433, 5, [(2, 4), (3, 3)]⟩,
    ⟨1733, 2, [(2, 2), (433, 1)]⟩,
    ⟨10399, 6, [(2, 1), (3, 1), (1733, 1)]⟩,
    ⟨12577, 10, [(2, 5), (3, 1), (131, 1)]⟩,
    ⟨79, 3, [(2, 1), (3, 1), (13, 1)]⟩,
    ⟨317, 2, [(2, 2), (79, 1)]⟩,
    ⟨15217, 10, [(2, 4), (3, 1), (317, 1)]⟩,
    ⟨18401, 3, [(2, 5), (5, 2), (23, 1)]⟩,
    ⟨359, 7, [(2, 1), (179, 1)]⟩,
    ⟨22259, 2, [(2, 1), (31, 1), (359, 1)]⟩,
    ⟨13463, 5, [(2, 1), (53, 1), (127, 1)]⟩,
    ⟨26927, 5, [(2, 1), (13463, 1)]⟩,
    ⟨32579, 6, [(2, 1), (7, 1), (13, 1), (179, 1)]⟩,
    ⟨379, 2, [(2, 1), (3, 3), (7, 1)]⟩,
    ⟨19709, 2, [(2, 2), (13, 1), (379, 1)]⟩,
    ⟨39419, 2, [(2, 1), (19709, 1)]⟩,
    ⟨149, 2, [(2, 2), (37, 1)]⟩,
    ⟨47681, 3, [(2, 6), (5, 1), (149, 1)]⟩,
    ⟨103, 5, [(2, 1), (3, 1), (17, 1)]⟩,
    ⟨7211, 2, [(2, 1), (5, 1), (7, 1), (103, 1)]⟩,
    ⟨57689, 3, [(2, 3), (7211, 1)]⟩,
    ⟨139, 2, [(2, 1), (3, 1), (23, 1)]⟩,
    ⟨69779, 2, [(2, 1), (139, 1), (251, 1)]⟩,
    ⟨67, 2, [(2, 1), (3, 1), (11, 1)]⟩,
    ⟨8443, 2, [(2, 1), (3, 2), (7, 1), (67, 1)]⟩,
    ⟨84431, 7, [(2, 1), (5, 1), (8443, 1)]⟩,
    ⟨1277, 2, [(2, 2), (11, 1), (29, 1)]⟩,
    ⟨102161, 6, [(2, 4), (5, 1), (1277, 1)]⟩,
    ⟨123601, 17, [(2, 4), (3, 1), (5, 2), (103, 1)]⟩,
    ⟨997, 7, [(2, 2), (3, 1), (83, 1)]⟩,
    ⟨149551, 3, [(2, 1), (3, 1), (5, 2), (997, 1)]⟩,
    ⟨180949, 2, [(2, 2), (3, 1), (17, 1), (887, 1)]⟩,
    ⟨401, 3, [(2, 4), (5, 2)]⟩,
    ⟨218947, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (401, 1)]⟩,
    ⟨659, 2, [(2, 1), (7, 1), (47, 1)]⟩,
    ⟨264919, 3, [(2, 1), (3, 1), (67, 1), (659, 1)]⟩,
    ⟨1303, 6, [(2, 1), (3, 1), (7, 1), (31, 1)]⟩,
    ⟨320539, 2, [(2, 1), (3, 1), (41, 1), (1303, 1)]⟩,
    ⟨387839, 7, [(2, 1), (11, 1), (17, 2), (61, 1)]⟩,
    ⟨257, 3, [(2, 8)]⟩,
    ⟨469283, 2, [(2, 1), (11, 1), (83, 1), (257, 1)]⟩,
    ⟨3943, 3, [(2, 1), (3, 3), (73, 1)]⟩,
    ⟨15773, 2, [(2, 2), (3943, 1)]⟩,
    ⟨567829, 2, [(2, 2), (3, 2), (15773, 1)]⟩,
    ⟨687073, 5, [(2, 5), (3, 1), (17, 1), (421, 1)]⟩,
    ⟨831329, 3, [(2, 5), (83, 1), (313, 1)]⟩,
    ⟨197, 2, [(2, 2), (7, 2)]⟩,
    ⟨1005883, 7, [(2, 1), (3, 1), (23, 1), (37, 1), (197, 1)]⟩,
    ⟨1217113, 10, [(2, 3), (3, 1), (13, 1), (47, 1), (83, 1)]⟩,
    ⟨409, 21, [(2, 3), (3, 1), (17, 1)]⟩,
    ⟨4909, 6, [(2, 2), (3, 1), (409, 1)]⟩,
    ⟨1472701, 2, [(2, 2), (3, 1), (5, 2), (4909, 1)]⟩,
    ⟨890969, 3, [(2, 3), (13, 2), (659, 1)]⟩,
    ⟨1781939, 2, [(2, 1), (890969, 1)]⟩,
    ⟨349, 2, [(2, 2), (3, 1), (29, 1)]⟩,
    ⟨193, 5, [(2, 6), (3, 1)]⟩,
    ⟨3089, 3, [(2, 4), (193, 1)]⟩,
    ⟨2156123, 2, [(2, 1), (349, 1), (3089, 1)]⟩,
    ⟨2608897, 5, [(2, 8), (3, 1), (43, 1), (79, 1)]⟩,
    ⟨75161, 3, [(2, 3), (5, 1), (1879, 1)]⟩,
    ⟨3156763, 3, [(2, 1), (3, 1), (7, 1), (75161, 1)]⟩,
    ⟨5701, 2, [(2, 2), (3, 1), (5, 2), (19, 1)]⟩,
    ⟨3819671, 7, [(2, 1), (5, 1), (67, 1), (5701, 1)]⟩,
    ⟨1319, 13, [(2, 1), (659, 1)]⟩,
    ⟨4621777, 7, [(2, 4), (3, 1), (73, 1), (1319, 1)]⟩,
    ⟨59, 2, [(2, 1), (29, 1)]⟩,
    ⟨2833, 5, [(2, 4), (3, 1), (59, 1)]⟩,
    ⟨5592343, 3, [(2, 1), (3, 1), (7, 1), (47, 1), (2833, 1)]⟩,
    ⟨977, 3, [(2, 4), (61, 1)]⟩,
    ⟨577, 5, [(2, 6), (3, 2)]⟩,
    ⟨3463, 3, [(2, 1), (3, 1), (577, 1)]⟩,
    ⟨6766703, 5, [(2, 1), (977, 1), (3463, 1)]⟩,
    ⟨307, 5, [(2, 1), (3, 2), (17, 1)]⟩,
    ⟨8187691, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (307, 1)]⟩,
    ⟨21169, 13, [(2, 4), (3, 3), (7, 2)]⟩,
    ⟨1651183, 5, [(2, 1), (3, 1), (13, 1), (21169, 1)]⟩,
    ⟨9907099, 2, [(2, 1), (3, 1), (1651183, 1)]⟩,
    ⟨1193, 3, [(2, 3), (149, 1)]⟩,
    ⟨38177, 3, [(2, 5), (1193, 1)]⟩,
    ⟨11987579, 2, [(2, 1), (157, 1), (38177, 1)]⟩,
    ⟨1051, 7, [(2, 1), (3, 1), (5, 2), (7, 1)]⟩,
    ⟨12613, 2, [(2, 2), (3, 1), (1051, 1)]⟩,
    ⟨14504951, 13, [(2, 1), (5, 2), (23, 1), (12613, 1)]⟩,
    ⟨3709, 2, [(2, 2), (3, 2), (103, 1)]⟩,
    ⟨17550989, 3, [(2, 2), (7, 1), (13, 2), (3709, 1)]⟩,
    ⟨137, 3, [(2, 3), (17, 1)]⟩,
    ⟨823, 3, [(2, 1), (3, 1), (137, 1)]⟩,
    ⟨6451, 3, [(2, 1), (3, 1), (5, 2), (43, 1)]⟩,
    ⟨21236693, 2, [(2, 2), (823, 1), (6451, 1)]⟩,
    ⟨277, 5, [(2, 2), (3, 1), (23, 1)]⟩,
    ⟨9419, 2, [(2, 1), (17, 1), (277, 1)]⟩,
    ⟨18839, 7, [(2, 1), (9419, 1)]⟩,
    ⟨25696397, 2, [(2, 2), (11, 1), (31, 1), (18839, 1)]⟩,
    ⟨31092629, 2, [(2, 2), (7, 1), (31, 1), (113, 1), (317, 1)]⟩,
    ⟨311, 17, [(2, 1), (5, 1), (31, 1)]⟩,
    ⟨11197, 2, [(2, 2), (3, 2), (311, 1)]⟩,
    ⟨268729, 7, [(2, 3), (3, 1), (11197, 1)]⟩,
    ⟨18811031, 13, [(2, 1), (5, 1), (7, 1), (268729, 1)]⟩,
    ⟨37622063, 5, [(2, 1), (18811031, 1)]⟩,
    ⟨91411, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (277, 1)]⟩,
    ⟨45522679, 3, [(2, 1), (3, 1), (83, 1), (91411, 1)]⟩,
    ⟨1663, 3, [(2, 1), (3, 1), (277, 1)]⟩,
    ⟨16631, 19, [(2, 1), (5, 1), (1663, 1)]⟩,
    ⟨99787, 2, [(2, 1), (3, 1), (16631, 1)]⟩,
    ⟨4590203, 2, [(2, 1), (23, 1), (99787, 1)]⟩,
    ⟨55082437, 2, [(2, 2), (3, 1), (4590203, 1)]⟩,
    ⟨4691, 2, [(2, 1), (5, 1), (7, 1), (67, 1)]⟩,
    ⟨66649729, 7, [(2, 7), (3, 1), (37, 1), (4691, 1)]⟩,
    ⟨2939, 2, [(2, 1), (13, 1), (113, 1)]⟩,
    ⟨80646161, 6, [(2, 4), (5, 1), (7, 3), (2939, 1)]⟩,
    ⟨171799, 3, [(2, 1), (3, 1), (11, 1), (19, 1), (137, 1)]⟩,
    ⟨97581833, 3, [(2, 3), (71, 1), (171799, 1)]⟩,
    ⟨337, 10, [(2, 4), (3, 1), (7, 1)]⟩,
    ⟨10949, 2, [(2, 2), (7, 1), (17, 1), (23, 1)]⟩,
    ⟨118074017, 3, [(2, 5), (337, 1), (10949, 1)]⟩]

theorem primeChain_prime : ∀ p ∈ primeChain, p.Prime :=
  primes_of_prattCertifiesAll primeChain primeChainCert (by decide +kernel)

theorem chainOK_primeChain : chainOK (25 :: primeChain) = true := by decide +kernel

/-- **Short-interval primes.** For every real `x ≥ 25` there is a prime `p` with
`x < p ≤ 1.21 x`. -/
theorem exists_prime_Ioc_mul (x : ℝ) (hx : 25 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ 1.21 * x := by
  by_cases hbig : 10 ^ 8 ≤ x
  · exact exists_prime_Ioc_large x hbig
  · push Not at hbig
    have hmem : (118074017 : ℕ) ∈ primeChain := by decide +kernel
    obtain ⟨p, hp, hxp, hpx⟩ := chainOK_cover primeChain 25 chainOK_primeChain x
      (by push_cast; linarith) ⟨118074017, hmem, by push_cast; linarith⟩
    exact ⟨p, primeChain_prime p hp, hxp, by linarith⟩

/-- Natural-number form: for `n ≥ 25` there is a prime `p` with `n < p` and `100 p ≤ 121 n`. -/
theorem exists_prime_Ioc_mul_nat (n : ℕ) (hn : 25 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ 100 * p ≤ 121 * n := by
  obtain ⟨p, hp, h1, h2⟩ := exists_prime_Ioc_mul n (by exact_mod_cast hn)
  refine ⟨p, hp, by exact_mod_cast h1, ?_⟩
  have : (100 * p : ℝ) ≤ 121 * n := by linarith
  exact_mod_cast this

end OpenProblemsLib.ShortIntervalPrimes
