import Mathlib
import OpenProblemsLib.Pratt
import OpenProblemsLib.ShortIntervalPrimes

/-!
# Nagura's theorem: a prime in `(x, 6x/5]` for every real `x ≥ 25`

J. Nagura, *On the interval containing at least one prime number*, Proc. Japan Acad. 28 (1952)
177–181. The proof here is not Nagura's; it sharpens Chebyshev's upper bound from
`ShortIntervalPrimes.lean` with one more step of the same weight.

Chebyshev's weight `E = E ν` (period 30, values in `{0, 1}`) equals 1 on `[1, 6)` and also on
`[7, 10)`. Hence `ψ x - ψ (x/6) + ψ (x/7) - ψ (x/10) ≤ U x`, and with Chebyshev's lower bound
at `x/7` and his upper bound at `x/10`,
`ψ x - ψ (x/6) ≤ (171/175) a x + O(log² x)`. Telescoping gives
`ψ x ≤ (1026/875) a x + O(log³ x)`, and `1026/875 = 1.17257… < 6/5`, so
`θ (6x/5) - θ x > 0` for `x ≥ 10^8`. A chain of 88 primes `29, 31, 37, …, 112189457`, each at
most `6/5` times the previous one (Pratt certificates checked in the kernel), covers
`x ∈ [25, 10^8)`.

Main results.
* `E_nu_eq_one_of_mem_Ico_7_10` : Chebyshev's weight is 1 on `[7, 10)`.
* `psi_diff_le_weighted2` : `ψ x - ψ (x/6) + ψ (x/7) - ψ (x/10) ≤ U x` for `x > 0`.
* `psi_diff_upper2` : `ψ x - ψ (x/6) ≤ (171/175) a x + 3 log² x + 10 log x + 160` for `x ≥ 300`.
* `psi_upper2` : `ψ x ≤ (1026/875) a x + (log x / log 6)(3 log² x + 10 log x + 160) + 1620`
  for `x ≥ 300`.
* `exists_prime_Ioc_six_fifths_large` : a prime in `(x, 6x/5]` for real `x ≥ 10^8`.
* `nagura` : a prime in `(x, 6x/5]` for real `x ≥ 25`.
* `nagura_nat` : for `n ≥ 25` a prime `p` with `n < p` and `5 p ≤ 6 n`.
* `nagura_nat_lt` : the same with `5 p < 6 n` (equality is impossible for a prime `p`).

Checked: everything above, axioms propext, Classical.choice, Quot.sound.
`E_nu_expand'` repeats a private lemma of `ShortIntervalPrimes.lean` (adapted from
PrimeNumberTheoremAnd, Apache 2.0, see that file's header); everything else here is new.
-/

namespace OpenProblemsLib.Nagura

open Real Finsupp Finset Chebyshev
open ArithmeticFunction hiding log
open OpenProblemsLib.ShortIntervalPrimes

/-! ## Chebyshev's weight on `[7, 10)` -/

/-- `E ν y` as floors (repeats the private `E_nu_expand` of `ShortIntervalPrimes`). -/
lemma E_nu_expand' (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

theorem E_nu_eq_one_of_mem_Ico_7_10 (y : ℝ) (h7 : 7 ≤ y) (h10 : y < 10) : E ν y = 1 := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  rw [E_nu_expand']
  simp only [Nat.floor_div_ofNat]
  have h1 : 7 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h7)
  have h2 : ⌊y⌋₊ < 10 := (Nat.floor_lt hy0).mpr (by exact_mod_cast h10)
  generalize ⌊y⌋₊ = m at h1 h2 ⊢
  interval_cases m <;> norm_num

/-! ## `ψ x - ψ (x/6) + ψ (x/7) - ψ (x/10) ≤ U x` -/

/-- `ψ (x/k)` as a sum over `n ≤ x` with an indicator. -/
lemma psi_div_eq (x k : ℝ) (hx : 0 ≤ x) (hk : 1 ≤ k) :
    ψ (x / k) = ∑ n ∈ Ioc 0 ⌊x⌋₊, if (n : ℝ) * k ≤ x then Λ n else 0 := by
  rw [← Finset.sum_filter, psi]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  have hk0 : 0 < k := by linarith
  have hxk : 0 ≤ x / k := div_nonneg hx hk0.le
  rw [Nat.le_floor_iff hxk, Nat.le_floor_iff hx, le_div_iff₀ hk0]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨⟨h0, by nlinarith⟩, h⟩
  · rintro ⟨⟨h0, _⟩, h⟩
    exact ⟨h0, h⟩

theorem psi_diff_le_weighted2 (x : ℝ) (hx : 0 < x) :
    ψ x - ψ (x / 6) + ψ (x / 7) - ψ (x / 10) ≤ U x := by
  have e1 := psi_div_eq x 1 hx.le le_rfl
  rw [div_one] at e1
  rw [e1, psi_div_eq x 6 hx.le (by norm_num), psi_div_eq x 7 hx.le (by norm_num),
    psi_div_eq x 10 hx.le (by norm_num)]
  unfold U
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  simp only [Finset.mem_Ioc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hn.2
  have hy1 : 1 ≤ x / n := (one_le_div hn0).mpr hnx
  have hE := E_nu_bound (x / n) (by linarith)
  have hL : 0 ≤ Λ n := vonMangoldt_nonneg
  have key : ∀ k : ℝ, ((n : ℝ) * k ≤ x ↔ k ≤ x / n) := by
    intro k
    rw [le_div_iff₀ hn0, mul_comm]
  simp only [show (n : ℝ) * 1 ≤ x by linarith, ↓reduceIte, key 6, key 7, key 10]
  by_cases h6 : (6 : ℝ) ≤ x / n
  · by_cases h7 : (7 : ℝ) ≤ x / n
    · by_cases h10 : (10 : ℝ) ≤ x / n
      · simp only [h6, h7, h10, ↓reduceIte]
        nlinarith [hE.1]
      · simp only [h6, h7, h10, ↓reduceIte]
        rw [E_nu_eq_one_of_mem_Ico_7_10 (x / n) h7 (by linarith)]
        linarith
    · have h10 : ¬ (10 : ℝ) ≤ x / n := fun h => h7 (by linarith)
      simp only [h6, h7, h10, ↓reduceIte]
      nlinarith [hE.1]
  · have h7 : ¬ (7 : ℝ) ≤ x / n := fun h => h6 (by linarith)
    have h10 : ¬ (10 : ℝ) ≤ x / n := fun h => h6 (by linarith)
    simp only [h6, h7, h10, ↓reduceIte]
    rw [E_nu_eq_one (x / n) ⟨hy1, by linarith⟩]
    linarith

/-! ## Sharper upper bound for `ψ` -/

lemma log_6_gt : 1.79 < log 6 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  linarith [log_2_gt, log_3_gt]

theorem psi_diff_upper2 (x : ℝ) (hx : 300 ≤ x) :
    ψ x - ψ (x / 6) ≤ 171 / 175 * a * x + (3 * log x ^ 2 + 10 * log x + 160) := by
  have hx0 : 0 < x := by linarith
  have hw := psi_diff_le_weighted2 x hx0
  have hU := (abs_sub_le_iff.mp (U_bound x (by linarith))).1
  have h7 := psi_lower (x / 7) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have h10 := psi_upper (x / 10) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hl7 : log (x / 7) ≤ log x := log_le_log (by positivity) (div_le_self hx0.le (by norm_num))
  have hl10 : log (x / 10) ≤ log x :=
    log_le_log (by positivity) (div_le_self hx0.le (by norm_num))
  have hl10' : 3 ≤ log (x / 10) := by
    have := log_le_log (by norm_num) (show (30 : ℝ) ≤ x / 10 by
      rw [le_div_iff₀ (by norm_num)]; linarith)
    linarith [log_30_gt]
  have h6 := log_6_gt
  have hq : (log (x / 10) / log 6) * (5 * log (x / 10) - 5) ≤ 3 * log x ^ 2 := by
    have hd : log (x / 10) / log 6 ≤ log (x / 10) / 1.79 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) h6.le
    have hd0 : 0 ≤ log (x / 10) / log 6 := div_nonneg (by linarith) (by linarith)
    calc (log (x / 10) / log 6) * (5 * log (x / 10) - 5)
        ≤ (log (x / 10) / log 6) * (5 * log (x / 10)) :=
          mul_le_mul_of_nonneg_left (by linarith) hd0
      _ ≤ (log (x / 10) / 1.79) * (5 * log (x / 10)) :=
          mul_le_mul_of_nonneg_right hd (by linarith)
      _ = (5 / 1.79) * (log (x / 10) * log (x / 10)) := by ring
      _ ≤ (5 / 1.79) * (log x * log x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hl10 hl10 (by linarith) (by linarith))
            (by norm_num)
      _ ≤ 3 * log x ^ 2 := by nlinarith [sq_nonneg (log x)]
  have e7 : a * (x / 7) = a * x / 7 := by ring
  have e10 : 6 / 5 * a * (x / 10) = 3 / 25 * (a * x) := by ring
  have e0 : 171 / 175 * a * x = 171 / 175 * (a * x) := by ring
  rw [e7] at h7
  rw [e10] at h10
  rw [e0]
  linarith

/-- Crude bound for `ψ` below 300, from Mathlib's `psi_le_const_mul_self`. -/
lemma psi_small300 (y : ℝ) (hy0 : 0 ≤ y) (hy : y < 300) : ψ y ≤ 1620 := by
  have h := psi_le_const_mul_self hy0
  have h4 : log 4 < 1.4 := by
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [log_2_lt]
  nlinarith [mul_le_mul_of_nonneg_right h4.le hy0]

lemma psi_tele2 (x : ℝ) (hx : 0 < x) : ∀ n : ℕ, (∀ i < n, 300 ≤ x / 6 ^ i) →
    ψ x ≤ ψ (x / 6 ^ n) +
      ∑ i ∈ range n, (171 / 175 * a * (x / 6 ^ i) + (3 * log x ^ 2 + 10 * log x + 160)) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have hn : 300 ≤ x / 6 ^ n := h n (by omega)
    have h2 := psi_diff_upper2 (x / 6 ^ n) hn
    have h3 : x / 6 ^ n / 6 = x / 6 ^ (n + 1) := by rw [pow_succ, div_div]
    rw [h3] at h2
    have h4 : log (x / 6 ^ n) ≤ log x := by
      apply log_le_log (by positivity)
      exact div_le_self hx.le (one_le_pow₀ (by norm_num))
    have h5 : 0 ≤ log (x / 6 ^ n) := log_nonneg (by linarith)
    have h6 : log (x / 6 ^ n) ^ 2 ≤ log x ^ 2 := pow_le_pow_left₀ h5 h4 2
    rw [sum_range_succ]
    linarith

/-- Sharper Chebyshev upper bound:
`ψ x ≤ (1026/875) a x + (log x / log 6)(3 log² x + 10 log x + 160) + 1620` for `x ≥ 300`. -/
theorem psi_upper2 (x : ℝ) (hx : 300 ≤ x) :
    ψ x ≤ 1026 / 875 * a * x + (log x / log 6) * (3 * log x ^ 2 + 10 * log x + 160) + 1620 := by
  have hx0 : 0 < x := by linarith
  have hex : ∃ n : ℕ, x / 6 ^ n < 300 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / 300) (by norm_num : (1 : ℝ) < 6)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by norm_num)] at hn
    linarith
  classical
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, x / 6 ^ n < 300 ∧ ∀ i < n, 300 ≤ x / 6 ^ i :=
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
  have hlogx : 0 ≤ log x := log_nonneg (by linarith)
  have ht := psi_tele2 x hx0 n hmin
  have hgs : ∑ i ∈ range n, 171 / 175 * a * (x / 6 ^ i) = 171 / 175 * a * (6 / 5 * x * (1 - 1 / 6 ^ n)) := by
    rw [← Finset.mul_sum, geom_six]
  rw [sum_add_distrib, hgs, sum_const, card_range, nsmul_eq_mul] at ht
  have ha : 0 ≤ a := le_trans (by norm_num) a_bound.1
  have hg : 0 ≤ a * (6 / 5 * x) * (1 / 6 ^ n) := by positivity
  have hP : 0 ≤ 3 * log x ^ 2 + 10 * log x + 160 := by positivity
  have hm : (n : ℝ) * (3 * log x ^ 2 + 10 * log x + 160) ≤
      (log x / log 6) * (3 * log x ^ 2 + 10 * log x + 160) :=
    mul_le_mul_of_nonneg_right hnle hP
  have hs := psi_small300 (x / 6 ^ n) (by positivity) hn
  nlinarith

/-! ## A prime in `(x, 6x/5]` for large `x` -/

/-- Write `x ≥ 10^8` as `10^8 v^4` with `v ≥ 1`. -/
lemma exists_fourth_root (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    ∃ v : ℝ, 1 ≤ v ∧ x = 10 ^ 8 * v ^ 4 ∧ √x = 10 ^ 4 * v ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 ≤ √x := sqrt_nonneg x
  have hss : √x * √x = x := mul_self_sqrt hx0.le
  have hs4 : 10 ^ 4 ≤ √x := by nlinarith
  have hu0 : 0 ≤ √x / 10 ^ 4 := by positivity
  set v := √(√x / 10 ^ 4) with hv
  have hvv : v * v = √x / 10 ^ 4 := mul_self_sqrt hu0
  have hsv : √x = 10 ^ 4 * v ^ 2 := by rw [sq, hvv]; ring
  refine ⟨v, ?_, ?_, hsv⟩
  · rw [hv, Real.one_le_sqrt, le_div_iff₀ (by norm_num)]
    linarith
  · calc x = √x * √x := hss.symm
      _ = 10 ^ 8 * v ^ 4 := by rw [hsv]; ring

/-- `log (6/5 · 10^8 v^4) ≤ 18.63 v` for `v ≥ 1`. -/
lemma log_fourth_root (v : ℝ) (hv : 1 ≤ v) : log (6 / 5 * (10 ^ 8 * v ^ 4)) ≤ 18.63 * v := by
  have hlogv : log v ≤ v - 1 := log_le_sub_one_of_pos (by linarith)
  have h104 : 8 * log 10 ≤ 18.4208 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
    linarith [log_2_lt, log_5_lt]
  have h65 : log (6 / 5 : ℝ) ≤ 0.2 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6 / 5); linarith
  have e : log (6 / 5 * (10 ^ 8 * v ^ 4)) = log (6 / 5) + 8 * log 10 + 4 * log v := by
    rw [log_mul (by norm_num) (by positivity), log_mul (by norm_num) (by positivity)]
    simp only [Real.log_pow]
    push_cast
    ring
  linarith

/-- The `O(log³)` term of `psi_upper2` at `L ≤ 18.63 v`, as a multiple of `v^4`. -/
lemma cubic_fourth_root (v : ℝ) (hv : 1 ≤ v) :
    (18.63 * v / 1.79) * (3 * (18.63 * v) ^ 2 + 10 * (18.63 * v) + 160) ≤ 14500 * v ^ 4 := by
  have hv2 : v ≤ v ^ 2 := by nlinarith
  have hv3 : v ^ 2 ≤ v ^ 3 := by nlinarith
  have hv4 : v ^ 3 ≤ v ^ 4 := by nlinarith
  have e : (18.63 * v / 1.79) * (3 * (18.63 * v) ^ 2 + 10 * (18.63 * v) + 160) =
      18.63 / 1.79 * (3 * 18.63 ^ 2) * v ^ 3 + 18.63 / 1.79 * (10 * 18.63) * v ^ 2 +
        18.63 / 1.79 * 160 * v := by ring
  rw [e]
  norm_num
  linarith

theorem exists_prime_Ioc_six_fifths_large (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ 6 / 5 * x := by
  apply exists_prime_of_theta_lt
  have hx0 : 0 < x := by linarith
  have hlow := psi_lower (6 / 5 * x) (by linarith)
  have hup := psi_upper2 x (by linarith)
  have hpt := psi_sub_theta_le (x := 6 / 5 * x) (by linarith)
  have htp := theta_le_psi x
  obtain ⟨ha1, _⟩ := a_bound
  obtain ⟨v, hv1, hxv, hsv⟩ := exists_fourth_root x hx
  have hv2 : v ≤ v ^ 2 := by nlinarith
  have hv3 : v ^ 2 ≤ v ^ 3 := by nlinarith
  have hv4 : v ^ 3 ≤ v ^ 4 := by nlinarith
  have hLM : log (6 / 5 * x) ≤ 18.63 * v := by rw [hxv]; exact log_fourth_root v hv1
  have hlogx0 : 0 ≤ log x := log_nonneg (by linarith)
  have hlogxL : log x ≤ log (6 / 5 * x) := log_le_log hx0 (by linarith)
  have hL0 : 0 ≤ log (6 / 5 * x) := by linarith
  -- `2 √(6x/5) log(6x/5) ≤ 2.2 √x · 18.63 v`.
  --
  have hsr : √(6 / 5 * x) ≤ 1.1 * √x := by
    have h1 : √(6 / 5 * x) ≤ √(1.21 * x) := Real.sqrt_le_sqrt (by linarith)
    have h2 : √(1.21 * x) = 1.1 * √x := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1.21), show (1.21 : ℝ) = 1.1 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    linarith
  have hT1 : 2 * √(6 / 5 * x) * log (6 / 5 * x) ≤ 409860 * v ^ 3 := by
    have h1 : 2 * √(6 / 5 * x) * log (6 / 5 * x) ≤ 2 * (1.1 * √x) * log (6 / 5 * x) :=
      mul_le_mul_of_nonneg_right (by linarith) hL0
    have h2 : √x * log (6 / 5 * x) ≤ √x * (18.63 * v) :=
      mul_le_mul_of_nonneg_left hLM (sqrt_nonneg x)
    have h3 : √x * (18.63 * v) = 186300 * v ^ 3 := by rw [hsv]; ring
    have h4 : 2 * (1.1 * √x) * log (6 / 5 * x) = 2.2 * (√x * log (6 / 5 * x)) := by ring
    linarith
  -- The `O(log³ x)` term of `psi_upper2`.
  --
  have hT2 : (log x / log 6) * (3 * log x ^ 2 + 10 * log x + 160) ≤ 14500 * v ^ 4 := by
    have h6 := log_6_gt
    have hlv : log x ≤ 18.63 * v := by linarith
    have hd : log x / log 6 ≤ 18.63 * v / 1.79 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      calc log x * 1.79 ≤ log x * log 6 := mul_le_mul_of_nonneg_left h6.le hlogx0
        _ ≤ 18.63 * v * log 6 := mul_le_mul_of_nonneg_right hlv (by linarith)
    have hd0 : 0 ≤ log x / log 6 := div_nonneg hlogx0 (by linarith)
    have hP : 3 * log x ^ 2 + 10 * log x + 160 ≤ 3 * (18.63 * v) ^ 2 + 10 * (18.63 * v) + 160 := by
      have : log x ^ 2 ≤ (18.63 * v) ^ 2 := pow_le_pow_left₀ hlogx0 hlv 2
      linarith
    have hP0 : 0 ≤ 3 * log x ^ 2 + 10 * log x + 160 := by positivity
    calc (log x / log 6) * (3 * log x ^ 2 + 10 * log x + 160)
        ≤ (18.63 * v / 1.79) * (3 * (18.63 * v) ^ 2 + 10 * (18.63 * v) + 160) :=
          mul_le_mul hd hP hP0 (by positivity)
      _ ≤ 14500 * v ^ 4 := cubic_fourth_root v hv1
  have hax : 0.92129 * x ≤ a * x := mul_le_mul_of_nonneg_right ha1 hx0.le
  have e1 : a * (6 / 5 * x) = 6 / 5 * (a * x) := by ring
  have e2 : 1026 / 875 * a * x = 1026 / 875 * (a * x) := by ring
  rw [e1] at hlow
  rw [e2] at hup
  linarith

/-! ## Small `x`: a chain of certified primes -/

/-- `chainOK65 (a :: l)`: the list increases and each entry is at most `6/5` times the previous. -/
def chainOK65 : List ℕ → Bool
  | a :: b :: l => decide (a < b) && decide (5 * b ≤ 6 * a) && chainOK65 (b :: l)
  | _ => true

theorem chainOK65_cover : ∀ (l : List ℕ) (a : ℕ), chainOK65 (a :: l) = true →
    ∀ x : ℝ, (a : ℝ) ≤ x → (∃ p ∈ l, x < p) → ∃ p ∈ l, x < p ∧ 5 * (p : ℝ) ≤ 6 * x := by
  intro l
  induction l with
  | nil =>
    intro a _ x _ h
    obtain ⟨p, hp, _⟩ := h
    simp at hp
  | cons b l ih =>
    intro a hc x hax hex
    simp only [chainOK65, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨_, hba⟩, hc⟩ := hc
    by_cases hxb : x < b
    · refine ⟨b, by simp, hxb, ?_⟩
      have : (5 * b : ℝ) ≤ 6 * a := by exact_mod_cast hba
      linarith
    · push Not at hxb
      obtain ⟨p, hp, hxp⟩ := hex
      rcases List.mem_cons.mp hp with rfl | hp'
      · linarith
      · obtain ⟨q, hq, h⟩ := ih b hc x hxb ⟨p, hp', hxp⟩
        exact ⟨q, List.mem_cons_of_mem _ hq, h⟩

/-- 88 primes from 29 to 112189457, each the largest prime at most `6/5` times the previous. -/
def naguraChain : List ℕ :=
  [29, 31, 37, 43, 47, 53, 61, 73, 83, 97, 113, 131, 157, 181, 211, 251, 293, 349, 409, 487, 577,
   691, 829, 991, 1187, 1423, 1699, 2029, 2423, 2903, 3469, 4159, 4987, 5981, 7177, 8609, 10321,
   12379, 14851, 17807, 21347, 25609, 30727, 36871, 44221, 53051, 63659, 76387, 91639, 109961,
   131947, 158329, 189989, 227977, 273569, 328277, 393931, 472711, 567209, 680633, 816743,
   980081, 1176089, 1411297, 1693553, 2032253, 2438693, 2926421, 3511693, 4214009, 5056781,
   6068137, 7281751, 8738101, 10485721, 12582853, 15099419, 18119291, 21743131, 26091727,
   31310047, 37572053, 45086453, 54103739, 64924481, 77909357, 93491221, 112189457]

/-- Pratt certificate for every prime in `naguraChain` (from `tools/pratt_cert.py`). -/
def naguraChainCert : List PrattStep :=
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
  ⟨349, 2, [(2, 2), (3, 1), (29, 1)]⟩,
  ⟨17, 3, [(2, 4)]⟩,
  ⟨409, 21, [(2, 3), (3, 1), (17, 1)]⟩,
  ⟨487, 3, [(2, 1), (3, 5)]⟩,
  ⟨577, 5, [(2, 6), (3, 2)]⟩,
  ⟨691, 3, [(2, 1), (3, 1), (5, 1), (23, 1)]⟩,
  ⟨829, 2, [(2, 2), (3, 2), (23, 1)]⟩,
  ⟨991, 6, [(2, 1), (3, 2), (5, 1), (11, 1)]⟩,
  ⟨593, 3, [(2, 4), (37, 1)]⟩,
  ⟨1187, 2, [(2, 1), (593, 1)]⟩,
  ⟨79, 3, [(2, 1), (3, 1), (13, 1)]⟩,
  ⟨1423, 3, [(2, 1), (3, 2), (79, 1)]⟩,
  ⟨283, 3, [(2, 1), (3, 1), (47, 1)]⟩,
  ⟨1699, 3, [(2, 1), (3, 1), (283, 1)]⟩,
  ⟨2029, 2, [(2, 2), (3, 1), (13, 2)]⟩,
  ⟨173, 2, [(2, 2), (43, 1)]⟩,
  ⟨2423, 5, [(2, 1), (7, 1), (173, 1)]⟩,
  ⟨1451, 2, [(2, 1), (5, 2), (29, 1)]⟩,
  ⟨2903, 5, [(2, 1), (1451, 1)]⟩,
  ⟨3469, 2, [(2, 2), (3, 1), (17, 2)]⟩,
  ⟨4159, 3, [(2, 1), (3, 3), (7, 1), (11, 1)]⟩,
  ⟨277, 5, [(2, 2), (3, 1), (23, 1)]⟩,
  ⟨4987, 2, [(2, 1), (3, 2), (277, 1)]⟩,
  ⟨5981, 3, [(2, 2), (5, 1), (13, 1), (23, 1)]⟩,
  ⟨7177, 10, [(2, 3), (3, 1), (13, 1), (23, 1)]⟩,
  ⟨67, 2, [(2, 1), (3, 1), (11, 1)]⟩,
  ⟨269, 2, [(2, 2), (67, 1)]⟩,
  ⟨8609, 3, [(2, 5), (269, 1)]⟩,
  ⟨10321, 7, [(2, 4), (3, 1), (5, 1), (43, 1)]⟩,
  ⟨103, 5, [(2, 1), (3, 1), (17, 1)]⟩,
  ⟨1031, 14, [(2, 1), (5, 1), (103, 1)]⟩,
  ⟨2063, 5, [(2, 1), (1031, 1)]⟩,
  ⟨12379, 2, [(2, 1), (3, 1), (2063, 1)]⟩,
  ⟨14851, 2, [(2, 1), (3, 3), (5, 2), (11, 1)]⟩,
  ⟨307, 5, [(2, 1), (3, 2), (17, 1)]⟩,
  ⟨17807, 5, [(2, 1), (29, 1), (307, 1)]⟩,
  ⟨821, 2, [(2, 2), (5, 1), (41, 1)]⟩,
  ⟨21347, 2, [(2, 1), (13, 1), (821, 1)]⟩,
  ⟨25609, 7, [(2, 3), (3, 1), (11, 1), (97, 1)]⟩,
  ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩,
  ⟨569, 3, [(2, 3), (71, 1)]⟩,
  ⟨30727, 3, [(2, 1), (3, 3), (569, 1)]⟩,
  ⟨1229, 2, [(2, 2), (307, 1)]⟩,
  ⟨36871, 15, [(2, 1), (3, 1), (5, 1), (1229, 1)]⟩,
  ⟨44221, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (67, 1)]⟩,
  ⟨1061, 2, [(2, 2), (5, 1), (53, 1)]⟩,
  ⟨53051, 6, [(2, 1), (5, 2), (1061, 1)]⟩,
  ⟨2273, 3, [(2, 5), (71, 1)]⟩,
  ⟨4547, 2, [(2, 1), (2273, 1)]⟩,
  ⟨63659, 2, [(2, 1), (7, 1), (4547, 1)]⟩,
  ⟨439, 15, [(2, 1), (3, 1), (73, 1)]⟩,
  ⟨76387, 3, [(2, 1), (3, 1), (29, 1), (439, 1)]⟩,
  ⟨1697, 3, [(2, 5), (53, 1)]⟩,
  ⟨91639, 3, [(2, 1), (3, 3), (1697, 1)]⟩,
  ⟨19, 2, [(2, 1), (3, 2)]⟩,
  ⟨229, 6, [(2, 2), (3, 1), (19, 1)]⟩,
  ⟨2749, 6, [(2, 2), (3, 1), (229, 1)]⟩,
  ⟨109961, 3, [(2, 3), (5, 1), (2749, 1)]⟩,
  ⟨733, 6, [(2, 2), (3, 1), (61, 1)]⟩,
  ⟨21991, 3, [(2, 1), (3, 1), (5, 1), (733, 1)]⟩,
  ⟨131947, 2, [(2, 1), (3, 1), (21991, 1)]⟩,
  ⟨158329, 13, [(2, 3), (3, 3), (733, 1)]⟩,
  ⟨1979, 2, [(2, 1), (23, 1), (43, 1)]⟩,
  ⟨47497, 5, [(2, 3), (3, 1), (1979, 1)]⟩,
  ⟨189989, 2, [(2, 2), (47497, 1)]⟩,
  ⟨59, 2, [(2, 1), (29, 1)]⟩,
  ⟨227977, 5, [(2, 3), (3, 1), (7, 1), (23, 1), (59, 1)]⟩,
  ⟨273569, 3, [(2, 5), (83, 1), (103, 1)]⟩,
  ⟨107, 2, [(2, 1), (53, 1)]⟩,
  ⟨328277, 3, [(2, 2), (13, 1), (59, 1), (107, 1)]⟩,
  ⟨1459, 3, [(2, 1), (3, 6)]⟩,
  ⟨393931, 2, [(2, 1), (3, 3), (5, 1), (1459, 1)]⟩,
  ⟨2251, 7, [(2, 1), (3, 2), (5, 3)]⟩,
  ⟨472711, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (2251, 1)]⟩,
  ⟨709, 2, [(2, 2), (3, 1), (59, 1)]⟩,
  ⟨70901, 2, [(2, 2), (5, 2), (709, 1)]⟩,
  ⟨567209, 3, [(2, 3), (70901, 1)]⟩,
  ⟨149, 2, [(2, 2), (37, 1)]⟩,
  ⟨571, 3, [(2, 1), (3, 1), (5, 1), (19, 1)]⟩,
  ⟨680633, 3, [(2, 3), (149, 1), (571, 1)]⟩,
  ⟨9497, 3, [(2, 3), (1187, 1)]⟩,
  ⟨816743, 5, [(2, 1), (43, 1), (9497, 1)]⟩,
  ⟨12251, 2, [(2, 1), (5, 3), (7, 2)]⟩,
  ⟨980081, 3, [(2, 4), (5, 1), (12251, 1)]⟩,
  ⟨241, 7, [(2, 4), (3, 1), (5, 1)]⟩,
  ⟨147011, 6, [(2, 1), (5, 1), (61, 1), (241, 1)]⟩,
  ⟨1176089, 3, [(2, 3), (147011, 1)]⟩,
  ⟨1411297, 7, [(2, 5), (3, 1), (61, 1), (241, 1)]⟩,
  ⟨15121, 11, [(2, 4), (3, 3), (5, 1), (7, 1)]⟩,
  ⟨1693553, 3, [(2, 4), (7, 1), (15121, 1)]⟩,
  ⟨197, 2, [(2, 2), (7, 2)]⟩,
  ⟨1289, 6, [(2, 3), (7, 1), (23, 1)]⟩,
  ⟨2579, 2, [(2, 1), (1289, 1)]⟩,
  ⟨2032253, 2, [(2, 2), (197, 1), (2579, 1)]⟩,
  ⟨191, 19, [(2, 1), (5, 1), (19, 1)]⟩,
  ⟨609673, 5, [(2, 3), (3, 1), (7, 1), (19, 1), (191, 1)]⟩,
  ⟨2438693, 2, [(2, 2), (609673, 1)]⟩,
  ⟨373, 2, [(2, 2), (3, 1), (31, 1)]⟩,
  ⟨1493, 2, [(2, 2), (373, 1)]⟩,
  ⟨20903, 5, [(2, 1), (7, 1), (1493, 1)]⟩,
  ⟨2926421, 2, [(2, 2), (5, 1), (7, 1), (20903, 1)]⟩,
  ⟨151, 6, [(2, 1), (3, 1), (5, 2)]⟩,
  ⟨97547, 2, [(2, 1), (17, 1), (19, 1), (151, 1)]⟩,
  ⟨3511693, 2, [(2, 2), (3, 2), (97547, 1)]⟩,
  ⟨4021, 2, [(2, 2), (3, 1), (5, 1), (67, 1)]⟩,
  ⟨4214009, 3, [(2, 3), (131, 1), (4021, 1)]⟩,
  ⟨10993, 7, [(2, 4), (3, 1), (229, 1)]⟩,
  ⟨5056781, 2, [(2, 2), (5, 1), (23, 1), (10993, 1)]⟩,
  ⟨6068137, 7, [(2, 3), (3, 1), (23, 1), (10993, 1)]⟩,
  ⟨7281751, 7, [(2, 1), (3, 1), (5, 3), (7, 1), (19, 1), (73, 1)]⟩,
  ⟨8738101, 2, [(2, 2), (3, 2), (5, 2), (7, 1), (19, 1), (73, 1)]⟩,
  ⟨10485721, 23, [(2, 3), (3, 3), (5, 1), (7, 1), (19, 1), (73, 1)]⟩,
  ⟨1048571, 2, [(2, 1), (5, 1), (23, 1), (47, 1), (97, 1)]⟩,
  ⟨12582853, 5, [(2, 2), (3, 1), (1048571, 1)]⟩,
  ⟨263, 5, [(2, 1), (131, 1)]⟩,
  ⟨463, 3, [(2, 1), (3, 1), (7, 1), (11, 1)]⟩,
  ⟨243539, 2, [(2, 1), (263, 1), (463, 1)]⟩,
  ⟨15099419, 2, [(2, 1), (31, 1), (243539, 1)]⟩,
  ⟨6163, 3, [(2, 1), (3, 1), (13, 1), (79, 1)]⟩,
  ⟨258847, 3, [(2, 1), (3, 1), (7, 1), (6163, 1)]⟩,
  ⟨18119291, 2, [(2, 1), (5, 1), (7, 1), (258847, 1)]⟩,
  ⟨89, 3, [(2, 3), (11, 1)]⟩,
  ⟨179, 2, [(2, 1), (89, 1)]⟩,
  ⟨4049, 3, [(2, 4), (11, 1), (23, 1)]⟩,
  ⟨21743131, 2, [(2, 1), (3, 1), (5, 1), (179, 1), (4049, 1)]⟩,
  ⟨8053, 2, [(2, 2), (3, 1), (11, 1), (61, 1)]⟩,
  ⟨4348621, 6, [(2, 2), (3, 3), (5, 1), (8053, 1)]⟩,
  ⟨26091727, 3, [(2, 1), (3, 1), (4348621, 1)]⟩,
  ⟨139, 2, [(2, 1), (3, 1), (23, 1)]⟩,
  ⟨6257, 3, [(2, 4), (17, 1), (23, 1)]⟩,
  ⟨1739447, 5, [(2, 1), (139, 1), (6257, 1)]⟩,
  ⟨31310047, 3, [(2, 1), (3, 2), (1739447, 1)]⟩,
  ⟨661, 2, [(2, 2), (3, 1), (5, 1), (11, 1)]⟩,
  ⟨46271, 7, [(2, 1), (5, 1), (7, 1), (661, 1)]⟩,
  ⟨37572053, 2, [(2, 2), (7, 1), (29, 1), (46271, 1)]⟩,
  ⟨163, 2, [(2, 1), (3, 4)]⟩,
  ⟨461, 2, [(2, 2), (5, 1), (23, 1)]⟩,
  ⟨69151, 11, [(2, 1), (3, 1), (5, 2), (461, 1)]⟩,
  ⟨45086453, 2, [(2, 2), (163, 1), (69151, 1)]⟩,
  ⟨5419, 3, [(2, 1), (3, 2), (7, 1), (43, 1)]⟩,
  ⟨130057, 5, [(2, 3), (3, 1), (5419, 1)]⟩,
  ⟨2080913, 3, [(2, 4), (130057, 1)]⟩,
  ⟨54103739, 2, [(2, 1), (13, 1), (2080913, 1)]⟩,
  ⟨1811, 6, [(2, 1), (5, 1), (181, 1)]⟩,
  ⟨3623, 5, [(2, 1), (1811, 1)]⟩,
  ⟨202889, 3, [(2, 3), (7, 1), (3623, 1)]⟩,
  ⟨64924481, 3, [(2, 6), (5, 1), (202889, 1)]⟩,
  ⟨18427, 2, [(2, 1), (3, 1), (37, 1), (83, 1)]⟩,
  ⟨77909357, 2, [(2, 2), (7, 1), (151, 1), (18427, 1)]⟩,
  ⟨239, 7, [(2, 1), (7, 1), (17, 1)]⟩,
  ⟨479, 13, [(2, 1), (239, 1)]⟩,
  ⟨271, 6, [(2, 1), (3, 3), (5, 1)]⟩,
  ⟨3253, 2, [(2, 2), (3, 1), (271, 1)]⟩,
  ⟨93491221, 2, [(2, 2), (3, 1), (5, 1), (479, 1), (3253, 1)]⟩,
  ⟨2069, 2, [(2, 2), (11, 1), (47, 1)]⟩,
  ⟨3389, 3, [(2, 2), (7, 1), (11, 2)]⟩,
  ⟨112189457, 3, [(2, 4), (2069, 1), (3389, 1)]⟩]

theorem naguraChain_prime : ∀ p ∈ naguraChain, p.Prime :=
  primes_of_prattCertifiesAll naguraChain naguraChainCert (by decide +kernel)

theorem chainOK65_naguraChain : chainOK65 (25 :: naguraChain) = true := by decide +kernel

/-- **Nagura's theorem** (1952). For every real `x ≥ 25` there is a prime `p` with
`x < p ≤ 6x/5`. -/
theorem nagura (x : ℝ) (hx : 25 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ 6 / 5 * x := by
  by_cases hbig : 10 ^ 8 ≤ x
  · exact exists_prime_Ioc_six_fifths_large x hbig
  · push Not at hbig
    have hmem : (112189457 : ℕ) ∈ naguraChain := by decide +kernel
    obtain ⟨p, hp, hxp, hpx⟩ := chainOK65_cover naguraChain 25 chainOK65_naguraChain x
      (by push_cast; linarith) ⟨112189457, hmem, by push_cast; linarith⟩
    exact ⟨p, naguraChain_prime p hp, hxp, by linarith⟩

/-- Natural-number form: for `n ≥ 25` there is a prime `p` with `n < p` and `5 p ≤ 6 n`. -/
theorem nagura_nat (n : ℕ) (hn : 25 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p ≤ 6 * n := by
  obtain ⟨p, hp, h1, h2⟩ := nagura n (by exact_mod_cast hn)
  refine ⟨p, hp, by exact_mod_cast h1, ?_⟩
  have : (5 * p : ℝ) ≤ 6 * n := by linarith
  exact_mod_cast this

/-- Strict natural-number form: `5 p = 6 n` would make `p` even. -/
theorem nagura_nat_lt (n : ℕ) (hn : 25 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n := by
  obtain ⟨p, hp, h1, h2⟩ := nagura_nat n hn
  refine ⟨p, hp, h1, ?_⟩
  rcases Nat.lt_or_ge (5 * p) (6 * n) with h | h
  · exact h
  · have he : 5 * p = 6 * n := by omega
    have h2p : 2 ∣ p := by omega
    rcases hp.eq_one_or_self_of_dvd 2 h2p with h' | h' <;> omega

end OpenProblemsLib.Nagura
