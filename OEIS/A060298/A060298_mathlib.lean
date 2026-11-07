import Mathlib

/-
OEIS A060298: number of powers x^y (x, y > 1) with n digits, counted as pairs
(x, y) (16 = 2^4 = 4^2 counts twice; this reproduces the data, e.g. a(2) = 12).
Conjectures (R. G. Wilson v, 2012): a(2n)/10^n -> 1 - 1/sqrt 10 and
a(2n-1)/10^n -> 1/sqrt 10 - 1/10.

Main theorems.
* `A060298_even`: a(2n)/10^n -> 1 - 1/sqrt 10.
* `A060298_odd`:  a(2n+1)/10^(n+1) -> 1/sqrt 10 - 1/10 (the entry's a(2n-1)/10^n).

Route.  `a_bounds`: sq N <= a N <= sq N + 4N 3^N, where sq N counts squares
with N digits (pairs with y = 2) and pairs with y >= 3 have x < 3^N, y < 4N.
`sq_card`: sq N = isqrt(10^N - 1) - isqrt(10^(N-1) - 1), so
|a N - (r^N - r^(N-1))| <= 1 + 4N 3^N with r = sqrt 10, and 3 < r.

Checked: all of the above from the definition `a`.  Not checked: agreement
of `a` with the OEIS data (certificate/check.py).
-/

open Filter Topology

namespace A060298

/-- Pairs (x, y), x, y ≥ 2, with x^y having exactly N decimal digits. -/
def a (N : ℕ) : ℕ :=
  ((Finset.range (10 ^ N) ×ˢ Finset.range (10 ^ N)).filter
    (fun p : ℕ × ℕ => 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ 10 ^ (N - 1) ≤ p.1 ^ p.2 ∧ p.1 ^ p.2 < 10 ^ N)).card

/-- Squares with N digits, by their roots. -/
def sqset (N : ℕ) : Finset ℕ :=
  (Finset.range (10 ^ N)).filter (fun x => 10 ^ (N - 1) ≤ x ^ 2 ∧ x ^ 2 < 10 ^ N)

lemma sqset_eq (N : ℕ) :
    sqset N = Finset.Ico (Nat.sqrt (10 ^ (N - 1) - 1) + 1) (Nat.sqrt (10 ^ N - 1) + 1) := by
  have h1 : 0 < 10 ^ (N - 1) := by positivity
  have h2 : 0 < 10 ^ N := by positivity
  ext x
  simp only [sqset, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨-, hl, hu⟩
    refine ⟨?_, ?_⟩
    · have : Nat.sqrt (10 ^ (N - 1) - 1) < x := Nat.sqrt_lt'.mpr (by omega)
      omega
    · have : x ≤ Nat.sqrt (10 ^ N - 1) := Nat.le_sqrt'.mpr (by omega)
      omega
  · rintro ⟨hl, hu⟩
    have hl' : 10 ^ (N - 1) - 1 < x ^ 2 := Nat.sqrt_lt'.mp (by omega)
    have hu' : x ^ 2 ≤ 10 ^ N - 1 := Nat.le_sqrt'.mp (by omega)
    have hx : x ≤ x ^ 2 := Nat.le_self_pow two_ne_zero x
    exact ⟨by omega, by omega, by omega⟩

lemma sq_card (N : ℕ) :
    (sqset N).card = Nat.sqrt (10 ^ N - 1) + 1 - (Nat.sqrt (10 ^ (N - 1) - 1) + 1) := by
  rw [sqset_eq, Nat.card_Ico]

lemma a_lower (N : ℕ) (hN : 2 ≤ N) : (sqset N).card ≤ a N := by
  unfold a
  rw [← Finset.card_image_of_injective (sqset N) (f := fun x => (x, 2))
    (fun x y h => by simpa using h)]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_image, sqset, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨x, ⟨hx, hl, hu⟩, rfl⟩ := hp
  have h10 : 10 ≤ 10 ^ (N - 1) := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (N - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN' : 100 ≤ 10 ^ N := by
    calc 100 = 10 ^ 2 := by norm_num
      _ ≤ 10 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨hx, by omega⟩, ?_, le_refl _, hl, hu⟩
  nlinarith

lemma a_upper (N : ℕ) : a N ≤ (sqset N).card + 4 * N * 3 ^ N := by
  unfold a
  set S := (Finset.range (10 ^ N) ×ˢ Finset.range (10 ^ N)).filter
    (fun p : ℕ × ℕ => 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ 10 ^ (N - 1) ≤ p.1 ^ p.2 ∧ p.1 ^ p.2 < 10 ^ N)
  rw [← Finset.card_filter_add_card_filter_not (fun p : ℕ × ℕ => p.2 = 2)]
  apply add_le_add
  · rw [← Finset.card_image_of_injective (sqset N) (f := fun x => (x, 2))
      (fun x y h => by simpa using h)]
    apply Finset.card_le_card
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨⟨hx, -⟩, -, -, hl, hu⟩, h2⟩ := hp
    simp only [Finset.mem_image, sqset, Finset.mem_filter, Finset.mem_range]
    refine ⟨p.1, ⟨hx, ?_, ?_⟩, ?_⟩
    · rwa [h2] at hl
    · rwa [h2] at hu
    · ext <;> simp [h2]
  · calc _ ≤ (Finset.range (3 ^ N) ×ˢ Finset.range (4 * N)).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
          obtain ⟨⟨-, hx2, hy2, -, hu⟩, h2⟩ := hp
          have hy3 : 3 ≤ p.2 := by omega
          simp only [Finset.mem_product, Finset.mem_range]
          constructor
          · by_contra h
            replace h := not_lt.mp h
            have : 27 ^ N ≤ p.1 ^ p.2 := by
              calc 27 ^ N = (3 ^ N) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
                _ ≤ p.1 ^ 3 := Nat.pow_le_pow_left h 3
                _ ≤ p.1 ^ p.2 := Nat.pow_le_pow_right (by omega) hy3
            have : 10 ^ N ≤ 27 ^ N := Nat.pow_le_pow_left (by norm_num) N
            omega
          · by_contra h
            replace h := not_lt.mp h
            have : 16 ^ N ≤ p.1 ^ p.2 := by
              calc 16 ^ N = 2 ^ (4 * N) := by rw [pow_mul]; norm_num
                _ ≤ 2 ^ p.2 := Nat.pow_le_pow_right (by norm_num) h
                _ ≤ p.1 ^ p.2 := Nat.pow_le_pow_left hx2 _
            have : 10 ^ N ≤ 16 ^ N := Nat.pow_le_pow_left (by norm_num) N
            omega
      _ = 4 * N * 3 ^ N := by rw [Finset.card_product]; simp [mul_comm]

/-- Real bounds for the integer square root: s < √M ≤ s + 1, s = isqrt(M - 1). -/
lemma isqrt_bounds (M : ℕ) (hM : 1 ≤ M) :
    (Nat.sqrt (M - 1) : ℝ) < Real.sqrt M ∧ Real.sqrt M ≤ Nat.sqrt (M - 1) + 1 := by
  set s := Nat.sqrt (M - 1)
  have h1 : s * s ≤ M - 1 := Nat.sqrt_le (M - 1)
  have h2 : M - 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (M - 1)
  have h1' : (s : ℝ) * s < M := by
    have : s * s < M := by omega
    exact_mod_cast this
  have h2' : (M : ℝ) ≤ ((s : ℝ) + 1) * ((s : ℝ) + 1) := by
    have : M ≤ (s + 1) * (s + 1) := by omega
    exact_mod_cast this
  constructor
  · rw [Real.lt_sqrt (by positivity)]
    nlinarith
  · rw [Real.sqrt_le_left (by positivity)]
    nlinarith

lemma sqrt_pow10 (N : ℕ) : Real.sqrt ((10 : ℕ) ^ N : ℕ) = Real.sqrt 10 ^ N := by
  rw [show (((10 : ℕ) ^ N : ℕ) : ℝ) = (Real.sqrt 10 ^ N) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]; push_cast; ring]
  exact Real.sqrt_sq (by positivity)

/-- |a N - (r^N - r^(N-1))| ≤ 1 + 4N 3^N with r = √10, for N ≥ 2. -/
lemma a_approx (N : ℕ) (hN : 2 ≤ N) :
    |(a N : ℝ) - (Real.sqrt 10 ^ N - Real.sqrt 10 ^ (N - 1))| ≤ 1 + 4 * N * 3 ^ N := by
  have hlo := a_lower N hN
  have hhi := a_upper N
  rw [sq_card] at hlo hhi
  obtain ⟨u1, u2⟩ := isqrt_bounds (10 ^ N) (Nat.one_le_pow _ _ (by norm_num))
  obtain ⟨l1, l2⟩ := isqrt_bounds (10 ^ (N - 1)) (Nat.one_le_pow _ _ (by norm_num))
  rw [sqrt_pow10] at u1 u2 l1 l2
  have hle : Nat.sqrt (10 ^ (N - 1) - 1) ≤ Nat.sqrt (10 ^ N - 1) :=
    Nat.sqrt_le_sqrt (by
      have : 10 ^ (N - 1) ≤ 10 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
  have e : ((Nat.sqrt (10 ^ N - 1) + 1 - (Nat.sqrt (10 ^ (N - 1) - 1) + 1) : ℕ) : ℝ) =
      (Nat.sqrt (10 ^ N - 1) : ℝ) - Nat.sqrt (10 ^ (N - 1) - 1) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hlo' : ((Nat.sqrt (10 ^ N - 1) + 1 - (Nat.sqrt (10 ^ (N - 1) - 1) + 1) : ℕ) : ℝ) ≤ a N := by
    exact_mod_cast hlo
  have hhi' : (a N : ℝ) ≤ ((Nat.sqrt (10 ^ N - 1) + 1 - (Nat.sqrt (10 ^ (N - 1) - 1) + 1) : ℕ) : ℝ)
      + 4 * N * 3 ^ N := by
    exact_mod_cast hhi
  rw [e] at hlo' hhi'
  rw [abs_le]
  constructor <;> nlinarith

lemma r_gt3 : (3 : ℝ) < Real.sqrt 10 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

/-- a N / r^N → 1 - 1/r. -/
lemma main (r : ℝ) (hr : r = Real.sqrt 10) :
    Tendsto (fun N : ℕ => (a N : ℝ) / r ^ N) atTop (𝓝 (1 - 1 / r)) := by
  have r3 : 3 < r := hr ▸ r_gt3
  have rpos : 0 < r := by linarith
  have hq : 0 ≤ 3 / r ∧ 3 / r < 1 := ⟨by positivity, (div_lt_one rpos).mpr r3⟩
  have hinv : 0 ≤ 1 / r ∧ 1 / r < 1 := ⟨by positivity, (div_lt_one rpos).mpr (by linarith)⟩
  have t1 := tendsto_pow_atTop_nhds_zero_of_lt_one hinv.1 hinv.2
  have t2 := tendsto_self_mul_const_pow_of_lt_one hq.1 hq.2
  have tb : Tendsto (fun N : ℕ => (1 / r) ^ N + 4 * ((N : ℝ) * (3 / r) ^ N)) atTop (𝓝 0) := by
    simpa using t1.add (t2.const_mul 4)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ tb
  filter_upwards [eventually_ge_atTop 2] with N hN
  have h := a_approx N hN
  rw [← hr] at h
  have hrN : 0 < r ^ N := pow_pos rpos N
  have key : (a N : ℝ) / r ^ N - (1 - 1 / r) = ((a N : ℝ) - (r ^ N - r ^ (N - 1))) / r ^ N := by
    have : r ^ N = r ^ (N - 1) * r := by rw [← pow_succ]; congr 1; omega
    field_simp
    rw [this]; ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, key, abs_div, abs_of_pos hrN,
    abs_of_nonneg (by positivity), div_le_iff₀ hrN]
  calc _ ≤ 1 + 4 * (N : ℝ) * 3 ^ N := h
    _ = ((1 / r) ^ N + 4 * ((N : ℝ) * (3 / r) ^ N)) * r ^ N := by
      rw [div_pow, div_pow, one_pow]; field_simp

theorem A060298_even :
    Tendsto (fun n : ℕ => (a (2 * n) : ℝ) / 10 ^ n) atTop (𝓝 (1 - 1 / Real.sqrt 10)) := by
  have h := (main _ rfl).comp
    (Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun n hn => by omega⟩) :
      Tendsto (fun n : ℕ => 2 * n) atTop atTop)
  refine h.congr (fun n => ?_)
  simp only [Function.comp]
  rw [pow_mul, Real.sq_sqrt (by norm_num)]

theorem A060298_odd :
    Tendsto (fun n : ℕ => (a (2 * n + 1) : ℝ) / 10 ^ (n + 1)) atTop
      (𝓝 (1 / Real.sqrt 10 - 1 / 10)) := by
  have hs : Real.sqrt 10 * Real.sqrt 10 = 10 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 10 := by positivity
  have h := ((main _ rfl).comp
    (Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun n hn => by omega⟩) :
      Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop)).div_const (Real.sqrt 10)
  have hv : (1 - 1 / Real.sqrt 10) / Real.sqrt 10 = 1 / Real.sqrt 10 - 1 / 10 := by
    field_simp; linear_combination hs
  rw [hv] at h
  refine h.congr (fun n => ?_)
  simp only [Function.comp]
  rw [pow_succ, pow_mul, Real.sq_sqrt (by norm_num), pow_succ]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
