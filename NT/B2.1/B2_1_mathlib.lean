import Mathlib

/-
NT-B2.1 (Mathlib). Guy B2: is every n > 3 a sum of two deficient numbers (σ(m) < 2m)?
Since 1 is deficient, the natural statement is for every n ≥ 2.

Main theorem `B2_1_main`: ∀ n ≥ 2, ∃ a b, a + b = n ∧ 0 < a ∧ 0 < b ∧ σ 1 a < 2 * a ∧
σ 1 b < 2 * b, with σ = Mathlib's `ArithmeticFunction.sigma`.

Proof (first-moment / Markov bound, see README). For 0 < t < N put
rs N t = Σ_{d < N, d ∣ t, d ≠ 1} 1/d, so σ(t) = t (1 + rs N t) and t is deficient iff
rs N t < 1. Summing rs over a family of t and swapping the sums gives
Σ_d (1/d) · #{t in the family : d ∣ t}.
* Even n = 2K: pairs (2k+1, n − 2k − 1), k < K. If every pair had a non-deficient member then
  K ≤ 2 Σ_k rs(2k+1) ≤ 2 · 2K · Σ_{odd d ≥ 3} 1/d² ≤ 2 · 2K · 17/72 < K.
* Odd n ≥ 300: r ∈ {1, 5} with 3 ∤ n − 2r, c = n − 2r, K = c / 12, m_k = 6k + r, pairs
  (2 m_k, c − 12k), k < K. Both members' odd parts are coprime to 6, σ(2m) = 3σ(m), so a bad
  pair gives 1 ≤ 3 rs(m_k) + rs(c − 12k). Each divisor d (coprime to 6, d ≥ 5) hits at most
  K/d + 1 indices k, so K ≤ 4 (K/8 + 11/8 + (n+1)/200), false once K ≥ 23.
* 2 ≤ n < 300: kernel `decide` on σ (`B2_small`).

Outside Lean: nothing.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-! ### Reciprocal divisor sums -/

/-- Σ of 1/d over divisors d ≠ 1 of t with d < N. -/
def rs (N t : ℕ) : ℚ := ∑ d ∈ range N, if d ∣ t ∧ d ≠ 1 then (1 : ℚ) / d else 0

theorem B2_rs_nonneg (N t : ℕ) : 0 ≤ rs N t := by
  unfold rs
  apply Finset.sum_nonneg
  intro d _
  split_ifs <;> positivity

theorem B2_sigma_eq (N t : ℕ) (ht : 0 < t) (hN : t < N) :
    (σ 1 t : ℚ) = t * (1 + rs N t) := by
  have h1 : (σ 1 t : ℚ) = ∑ d ∈ t.divisors, ((t / d : ℕ) : ℚ) := by
    rw [sigma_eq_sum_div]; push_cast; simp
  have h2 : ∑ d ∈ t.divisors, ((t / d : ℕ) : ℚ) = ∑ d ∈ t.divisors, (t : ℚ) * (1 / d) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdt : d ∣ t := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℚ) ≠ 0 := by
      have : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      exact_mod_cast this
    rw [Nat.cast_div hdt hd0]; ring
  have h3 : ∑ d ∈ t.divisors, (1 : ℚ) / d =
      ∑ d ∈ range N, if d ∣ t then (1 : ℚ) / d else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h, _⟩; exact ⟨lt_of_le_of_lt (Nat.le_of_dvd ht h) hN, h⟩
    · rintro ⟨_, h⟩; exact ⟨h, Nat.pos_iff_ne_zero.mp ht⟩
  have h4 : (∑ d ∈ range N, if d ∣ t then (1 : ℚ) / d else 0) =
      ∑ d ∈ range N, ((if d = 1 then (1 : ℚ) else 0) +
        (if d ∣ t ∧ d ≠ 1 then (1 : ℚ) / d else 0)) := by
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : d = 1
    · subst h; simp
    · simp [h]
  rw [h1, h2, ← Finset.mul_sum, h3, h4, Finset.sum_add_distrib, Finset.sum_ite_eq']
  have : 1 ∈ range N := Finset.mem_range.mpr (by omega)
  simp [this, rs]

/-- A non-deficient t has rs ≥ 1. -/
theorem B2_rs_of_not_def (N t : ℕ) (ht : 0 < t) (hN : t < N) (h : ¬ σ 1 t < 2 * t) :
    1 ≤ rs N t := by
  have e := B2_sigma_eq N t ht hN
  have h' : (2 * t : ℚ) ≤ σ 1 t := by exact_mod_cast Nat.le_of_not_lt h
  have htq : (0 : ℚ) < t := by exact_mod_cast ht
  rw [e] at h'
  nlinarith

theorem B2_sigma_two_mul (m : ℕ) (hm : m % 2 = 1) : σ 1 (2 * m) = 3 * σ 1 m := by
  have hc : Nat.Coprime 2 m := by
    rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr hm
  rw [isMultiplicative_sigma.map_mul_of_coprime hc]
  have : σ 1 2 = 3 := by decide
  rw [this]

/-- If 2m is not deficient (m odd) then rs(m) ≥ 1/3. -/
theorem B2_rs_of_not_def_two (N m : ℕ) (hm0 : 0 < m) (hm : m % 2 = 1) (hN : m < N)
    (h : ¬ σ 1 (2 * m) < 2 * (2 * m)) : 1 ≤ 3 * rs N m := by
  rw [B2_sigma_two_mul m hm] at h
  have e := B2_sigma_eq N m hm0 hN
  have h' : (4 * m : ℚ) ≤ 3 * σ 1 m := by
    have := Nat.le_of_not_lt h
    exact_mod_cast (by omega : 4 * m ≤ 3 * σ 1 m)
  have htq : (0 : ℚ) < m := by exact_mod_cast hm0
  rw [e] at h'
  nlinarith

/-- Swapping the sums. -/
theorem B2_sum_rs (K N : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range K, rs N (f k) =
      ∑ d ∈ range N, (1 / (d : ℚ)) *
        (((range K).filter (fun k => d ∣ f k ∧ d ≠ 1)).card : ℚ) := by
  unfold rs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ### Counting lemmas -/

/-- Indices whose images are distinct positive multiples of d up to M: at most M / d. -/
theorem B2_card_multiples (s : Finset ℕ) (f : ℕ → ℕ) (d M : ℕ) (hd : 0 < d)
    (h : ∀ k ∈ s, d ∣ f k ∧ 0 < f k ∧ f k ≤ M) (hinj : Set.InjOn f s) :
    s.card ≤ M / d := by
  have := Finset.card_le_card_of_injOn (fun k => f k / d) (t := Finset.Icc 1 (M / d))
    (fun k hk => by
      obtain ⟨h1, h2, h3⟩ := h k hk
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd h2 h1) hd, Nat.div_le_div_right h3⟩)
    (fun k hk k' hk' e => by
      obtain ⟨h1, _, _⟩ := h k hk
      obtain ⟨h1', _, _⟩ := h k' hk'
      apply hinj hk hk'
      simp only at e
      rw [← Nat.div_mul_cancel h1, ← Nat.div_mul_cancel h1', e])
  simpa using this

/-- A subset of range K whose elements are pairwise congruent mod d has at most K/d + 1
elements. -/
theorem B2_card_ap (s : Finset ℕ) (K d : ℕ) (hs : s ⊆ range K)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x ≡ y [MOD d]) : s.card ≤ K / d + 1 := by
  have := Finset.card_le_card_of_injOn (fun k => k / d) (t := range (K / d + 1))
    (fun k hk => by
      have := Finset.mem_range.mp (hs hk)
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right this.le))
    (fun x hx y hy e => by
      simp only at e
      have hm : x % d = y % d := hc x hx y hy
      rw [← Nat.div_add_mod x d, ← Nat.div_add_mod y d, e, hm])
  simpa using this

/-! ### Tail sums -/

/-- 1/d² over odd d ≥ 5. -/
def v5 (d : ℕ) : ℚ := if d % 2 = 1 ∧ 5 ≤ d then 1 / (d : ℚ) ^ 2 else 0

theorem B2_v5_nonneg (d : ℕ) : 0 ≤ v5 d := by
  unfold v5; split_ifs <;> positivity

theorem B2_v5_tele (M : ℕ) (hM : 2 ≤ M) :
    ∑ d ∈ range (2 * M), v5 d ≤ 1 / 8 - 1 / (4 * M) := by
  induction M, hM using Nat.le_induction with
  | base => simp [Finset.sum_range_succ, v5]; norm_num
  | succ M hM ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have e1 : v5 (2 * M) = 0 := by unfold v5; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    have e2 : v5 (2 * M + 1) = 1 / ((2 * M + 1 : ℕ) : ℚ) ^ 2 := by
      unfold v5; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    rw [e1, e2]
    have hMq : (2 : ℚ) ≤ M := by exact_mod_cast hM
    have key : 1 / ((2 * M + 1 : ℕ) : ℚ) ^ 2 ≤ 1 / (4 * M) - 1 / (4 * ((M + 1 : ℕ) : ℚ)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast at key ⊢
    linarith

theorem B2_v5_sum (N : ℕ) : ∑ d ∈ range N, v5 d ≤ 1 / 8 := by
  have hsub : range N ⊆ range (2 * (N + 2)) := Finset.range_subset_range.mpr (by omega)
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => B2_v5_nonneg d)
  have h2 := B2_v5_tele (N + 2) (by omega)
  have h3 : (0 : ℚ) ≤ 1 / (4 * ((N + 2 : ℕ) : ℚ)) := by positivity
  linarith

/-- 1/d over d ≥ 5 coprime to 6. -/
def h6 (d : ℕ) : ℚ := if (d % 6 = 1 ∨ d % 6 = 5) ∧ 5 ≤ d then 1 / (d : ℚ) else 0

theorem B2_h6_nonneg (d : ℕ) : 0 ≤ h6 d := by
  unfold h6; split_ifs <;> positivity

set_option maxRecDepth 20000 in
theorem B2_h6_head : ∑ d ∈ range 200, h6 d ≤ 11 / 8 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h6]
  norm_num

theorem B2_h6_tail (j : ℕ) : ∑ d ∈ range (200 + j), h6 d ≤ 11 / 8 + j / 200 := by
  induction j with
  | zero => simpa using B2_h6_head
  | succ j ih =>
    rw [← add_assoc, Finset.sum_range_succ]
    have : h6 (200 + j) ≤ 1 / 200 := by
      unfold h6
      split_ifs
      · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; linarith [(j.cast_nonneg : (0 : ℚ) ≤ j)]
      · norm_num
    push_cast
    linarith

theorem B2_h6_sum (N : ℕ) : ∑ d ∈ range N, h6 d ≤ 11 / 8 + N / 200 := by
  rcases le_or_gt N 200 with hN | hN
  · have hsub : range N ⊆ range 200 := Finset.range_subset_range.mpr hN
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => B2_h6_nonneg d)
    have : (0 : ℚ) ≤ N / 200 := by positivity
    linarith [B2_h6_head]
  · obtain ⟨j, rfl⟩ : ∃ j, N = 200 + j := ⟨N - 200, by omega⟩
    have := B2_h6_tail j
    have : (j : ℚ) / 200 ≤ ((200 + j : ℕ) : ℚ) / 200 := by
      push_cast; linarith
    linarith

/-! ### Even n -/

theorem B2_even_count (K d : ℕ) :
    (1 / (d : ℚ)) * (((range K).filter (fun k => d ∣ 2 * k + 1 ∧ d ≠ 1)).card : ℚ) ≤
      2 * K * ((if d = 3 then 1 / 9 else 0) + v5 d) := by
  by_cases hd : d % 2 = 1 ∧ 3 ≤ d
  · have hc := B2_card_multiples ((range K).filter (fun k => d ∣ 2 * k + 1 ∧ d ≠ 1))
      (fun k => 2 * k + 1) d (2 * K) (by omega)
      (fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        exact ⟨hk.2.1, by omega, by omega⟩)
      (fun x _ y _ e => by simp only at e; omega)
    have hcq : (((range K).filter (fun k => d ∣ 2 * k + 1 ∧ d ≠ 1)).card : ℚ) ≤
        (2 * K : ℚ) / d := by
      calc _ ≤ (((2 * K) / d : ℕ) : ℚ) := by exact_mod_cast hc
        _ ≤ _ := by have := Nat.cast_div_le (α := ℚ) (m := 2 * K) (n := d); push_cast at this;
                    exact this
    have hdq : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    have hrhs : 2 * K * ((if d = 3 then (1 : ℚ) / 9 else 0) + v5 d) = 2 * K * (1 / (d : ℚ) ^ 2) := by
      unfold v5
      by_cases h3 : d = 3
      · subst h3; norm_num
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; ring
    rw [hrhs]
    calc (1 / (d : ℚ)) * _ ≤ (1 / (d : ℚ)) * ((2 * K : ℚ) / d) :=
          mul_le_mul_of_nonneg_left hcq (by positivity)
      _ = _ := by field_simp
  · have : (range K).filter (fun k => d ∣ 2 * k + 1 ∧ d ≠ 1) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro k _ ⟨h1, h2⟩
      apply hd
      rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
      · exfalso
        have : 2 ∣ 2 * k + 1 := dvd_trans ⟨j, by omega⟩ h1
        omega
      · exact ⟨by omega, by omega⟩
    rw [this]
    have : 0 ≤ v5 d := B2_v5_nonneg d
    have : (0 : ℚ) ≤ 2 * K * ((if d = 3 then (1 : ℚ) / 9 else 0) + v5 d) := by
      split_ifs <;> positivity
    simpa using this

theorem B2_even (K : ℕ) (hK : 1 ≤ K) : ∃ a b, a + b = 2 * K ∧ 0 < a ∧ 0 < b ∧
    σ 1 a < 2 * a ∧ σ 1 b < 2 * b := by
  by_contra hcon
  push Not at hcon
  set N := 2 * K + 1
  have hpt : ∀ k ∈ range K, (1 : ℚ) ≤ rs N (2 * k + 1) + rs N (2 * (K - 1 - k) + 1) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    have e : 2 * k + 1 + (2 * (K - 1 - k) + 1) = 2 * K := by omega
    by_cases ha : σ 1 (2 * k + 1) < 2 * (2 * k + 1)
    · have hb : ¬ σ 1 (2 * (K - 1 - k) + 1) < 2 * (2 * (K - 1 - k) + 1) := by
        intro hb
        exact absurd hb (Nat.not_lt.mpr (hcon _ _ e (by omega) (by omega) ha))
      have := B2_rs_of_not_def N _ (by omega) (by omega) hb
      linarith [B2_rs_nonneg N (2 * k + 1)]
    · have := B2_rs_of_not_def N _ (by omega) (by omega) ha
      linarith [B2_rs_nonneg N (2 * (K - 1 - k) + 1)]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  have hrefl : ∑ k ∈ range K, rs N (2 * (K - 1 - k) + 1) = ∑ k ∈ range K, rs N (2 * k + 1) :=
    Finset.sum_range_reflect (fun k => rs N (2 * k + 1)) K
  rw [hrefl, B2_sum_rs] at hsum
  have hb : ∑ d ∈ range N, (1 / (d : ℚ)) *
      (((range K).filter (fun k => d ∣ 2 * k + 1 ∧ d ≠ 1)).card : ℚ) ≤ 2 * K * (17 / 72) := by
    calc _ ≤ ∑ d ∈ range N, 2 * K * ((if d = 3 then (1 : ℚ) / 9 else 0) + v5 d) :=
          Finset.sum_le_sum (fun d _ => B2_even_count K d)
      _ = 2 * K * ((∑ d ∈ range N, if d = 3 then (1 : ℚ) / 9 else 0) +
            ∑ d ∈ range N, v5 d) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * K * (1 / 9 + 1 / 8) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (∑ d ∈ range N, if d = 3 then (1 : ℚ) / 9 else 0) ≤ 1 / 9 := by
            rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
          linarith [B2_v5_sum N]
      _ = _ := by ring
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  have hKq : (1 : ℚ) ≤ K := by exact_mod_cast hK
  linarith

/-! ### Odd n -/

theorem B2_coprime6 (d : ℕ) (h2 : d % 2 = 1) (h3 : d % 3 ≠ 0) : Nat.gcd d 12 = 1 ∧
    Nat.gcd d 6 = 1 := by
  have c2 : Nat.Coprime d 2 := by
    rw [Nat.coprime_two_right]; exact Nat.odd_iff.mpr h2
  have c3 : Nat.Coprime d 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; omega
  have c6 : Nat.Coprime d 6 := Nat.Coprime.mul_right c2 c3
  exact ⟨Nat.Coprime.mul_right c6 c2, c6⟩

/-- Generic per-divisor bound for an index family whose values are coprime to 6 and whose
indices are pairwise congruent mod d whenever d divides both values. -/
theorem B2_odd_count (K d : ℕ) (f : ℕ → ℕ)
    (hf : ∀ k < K, f k % 2 = 1 ∧ f k % 3 ≠ 0)
    (hcong : ∀ k < K, ∀ k' < K, d % 2 = 1 → d % 3 ≠ 0 → d ∣ f k → d ∣ f k' →
      k ≡ k' [MOD d]) :
    (1 / (d : ℚ)) * (((range K).filter (fun k => d ∣ f k ∧ d ≠ 1)).card : ℚ) ≤
      K * v5 d + h6 d := by
  by_cases hd : d % 2 = 1 ∧ d % 3 ≠ 0 ∧ 5 ≤ d
  · have hc := B2_card_ap ((range K).filter (fun k => d ∣ f k ∧ d ≠ 1)) K d
      (Finset.filter_subset _ _)
      (fun x hx y hy => by
        simp only [Finset.mem_filter, Finset.mem_range] at hx hy
        exact hcong x hx.1 y hy.1 hd.1 hd.2.1 hx.2.1 hy.2.1)
    have hcq : (((range K).filter (fun k => d ∣ f k ∧ d ≠ 1)).card : ℚ) ≤
        (K : ℚ) / d + 1 := by
      calc _ ≤ (((K / d : ℕ) : ℚ) + 1) := by exact_mod_cast hc
        _ ≤ _ := by linarith [Nat.cast_div_le (α := ℚ) (m := K) (n := d)]
    have e1 : v5 d = 1 / (d : ℚ) ^ 2 := by unfold v5; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    have e2 : h6 d = 1 / (d : ℚ) := by unfold h6; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    rw [e1, e2]
    have hdq : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    calc (1 / (d : ℚ)) * _ ≤ (1 / (d : ℚ)) * ((K : ℚ) / d + 1) :=
          mul_le_mul_of_nonneg_left hcq (by positivity)
      _ = _ := by field_simp
  · have : (range K).filter (fun k => d ∣ f k ∧ d ≠ 1) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro k hk ⟨h1, h2⟩
      have hk := Finset.mem_range.mp hk
      obtain ⟨f2, f3⟩ := hf k hk
      apply hd
      have d2 : d % 2 = 1 := by
        by_contra hc
        have : 2 ∣ f k := dvd_trans (Nat.dvd_of_mod_eq_zero (by omega)) h1
        omega
      have d3 : d % 3 ≠ 0 := by
        intro hc
        have : 3 ∣ f k := dvd_trans (Nat.dvd_of_mod_eq_zero hc) h1
        omega
      refine ⟨d2, d3, ?_⟩
      omega
    rw [this]
    have : 0 ≤ v5 d := B2_v5_nonneg d
    have : 0 ≤ h6 d := B2_h6_nonneg d
    have : (0 : ℚ) ≤ K * v5 d + h6 d := by positivity
    simpa using this

theorem B2_odd_sum (K N : ℕ) (f : ℕ → ℕ)
    (hf : ∀ k < K, f k % 2 = 1 ∧ f k % 3 ≠ 0)
    (hcong : ∀ d, ∀ k < K, ∀ k' < K, d % 2 = 1 → d % 3 ≠ 0 → d ∣ f k → d ∣ f k' →
      k ≡ k' [MOD d]) :
    ∑ k ∈ range K, rs N (f k) ≤ K / 8 + 11 / 8 + N / 200 := by
  rw [B2_sum_rs]
  calc _ ≤ ∑ d ∈ range N, ((K : ℚ) * v5 d + h6 d) :=
        Finset.sum_le_sum (fun d _ => B2_odd_count K d f hf (hcong d))
    _ = K * ∑ d ∈ range N, v5 d + ∑ d ∈ range N, h6 d := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ K * (1 / 8) + (11 / 8 + N / 200) := by
        have : (0 : ℚ) ≤ K := by positivity
        gcongr
        · exact B2_v5_sum N
        · exact B2_h6_sum N
    _ = _ := by ring

theorem B2_odd (n r : ℕ) (hn : n % 2 = 1) (hn300 : 300 ≤ n) (hr : r = 1 ∨ r = 5)
    (h3 : (n - 2 * r) % 3 ≠ 0) : ∃ a b, a + b = n ∧ 0 < a ∧ 0 < b ∧
    σ 1 a < 2 * a ∧ σ 1 b < 2 * b := by
  by_contra hcon
  push Not at hcon
  set c := n - 2 * r with hc
  set K := c / 12 with hK
  set N := n + 1
  have hc12 : ∀ k < K, 12 * k + 12 ≤ c := by intro k hk; omega
  -- each index gives a bad pair
  have hpt : ∀ k ∈ range K, (1 : ℚ) ≤ 3 * rs N (6 * k + r) + rs N (c - 12 * k) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    have h12 := hc12 k hk
    have e : 2 * (6 * k + r) + (c - 12 * k) = n := by omega
    have hm2 : (6 * k + r) % 2 = 1 := by omega
    by_cases ha : σ 1 (2 * (6 * k + r)) < 2 * (2 * (6 * k + r))
    · have hb : ¬ σ 1 (c - 12 * k) < 2 * (c - 12 * k) := by
        intro hb
        exact absurd hb (Nat.not_lt.mpr (hcon _ _ e (by omega) (by omega) ha))
      have := B2_rs_of_not_def N _ (by omega) (by omega) hb
      linarith [B2_rs_nonneg N (6 * k + r)]
    · have := B2_rs_of_not_def_two N _ (by omega) hm2 (by omega) ha
      linarith [B2_rs_nonneg N (c - 12 * k)]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hA := B2_odd_sum K N (fun k => 6 * k + r)
    (fun k _ => by constructor <;> omega)
    (fun d k _ k' _ d2 d3 h1 h2 => by
      have hg := (B2_coprime6 d d2 d3).2
      have e : 6 * k + r ≡ 6 * k' + r [MOD d] :=
        (Nat.modEq_zero_iff_dvd.mpr h1).trans (Nat.modEq_zero_iff_dvd.mpr h2).symm
      exact Nat.ModEq.cancel_left_of_coprime hg (Nat.ModEq.add_right_cancel' r e))
  have hB := B2_odd_sum K N (fun k => c - 12 * k)
    (fun k hk => by have := hc12 k hk; constructor <;> omega)
    (fun d k hk k' hk' d2 d3 h1 h2 => by
      have hg := (B2_coprime6 d d2 d3).1
      have s1 : c ≡ 12 * k [MOD d] := by
        have := (Nat.modEq_zero_iff_dvd.mpr h1).add_right (12 * k)
        rwa [Nat.sub_add_cancel (by have := hc12 k hk; omega), zero_add] at this
      have s2 : c ≡ 12 * k' [MOD d] := by
        have := (Nat.modEq_zero_iff_dvd.mpr h2).add_right (12 * k')
        rwa [Nat.sub_add_cancel (by have := hc12 k' hk'; omega), zero_add] at this
      exact Nat.ModEq.cancel_left_of_coprime hg (s1.symm.trans s2))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  have hKn : 12 * K + 12 + 2 * r ≥ n := by omega
  have hK23 : 23 ≤ K := by omega
  have hKq : (23 : ℚ) ≤ K := by exact_mod_cast hK23
  have hNq : ((N : ℕ) : ℚ) ≤ 12 * K + 23 := by
    have : N ≤ 12 * K + 23 := by omega
    exact_mod_cast this
  linarith

/-! ### Small n and the main theorem -/

def okB (n : ℕ) : Bool :=
  (List.range n).any fun a => decide (0 < a ∧ σ 1 a < 2 * a ∧ σ 1 (n - a) < 2 * (n - a))

theorem B2_small0 : ∀ i < 50, okB (i + 2) = true := by decide +kernel
theorem B2_small1 : ∀ i < 50, okB (i + 52) = true := by decide +kernel
theorem B2_small2 : ∀ i < 50, okB (i + 102) = true := by decide +kernel
theorem B2_small3 : ∀ i < 50, okB (i + 152) = true := by decide +kernel
theorem B2_small4 : ∀ i < 50, okB (i + 202) = true := by decide +kernel
theorem B2_small5 : ∀ i < 48, okB (i + 252) = true := by decide +kernel

theorem B2_small (n : ℕ) (h2 : 2 ≤ n) (h : n < 300) : ∃ a b, a + b = n ∧ 0 < a ∧ 0 < b ∧
    σ 1 a < 2 * a ∧ σ 1 b < 2 * b := by
  have hok : okB n = true := by
    rcases Nat.lt_or_ge n 52 with h0 | h0
    · have := B2_small0 (n - 2) (by omega); rwa [Nat.sub_add_cancel h2] at this
    rcases Nat.lt_or_ge n 102 with h1 | h1
    · have := B2_small1 (n - 52) (by omega); rwa [Nat.sub_add_cancel h0] at this
    rcases Nat.lt_or_ge n 152 with h1' | h1'
    · have := B2_small2 (n - 102) (by omega); rwa [Nat.sub_add_cancel h1] at this
    rcases Nat.lt_or_ge n 202 with h2' | h2'
    · have := B2_small3 (n - 152) (by omega); rwa [Nat.sub_add_cancel h1'] at this
    rcases Nat.lt_or_ge n 252 with h3 | h3
    · have := B2_small4 (n - 202) (by omega); rwa [Nat.sub_add_cancel h2'] at this
    · have := B2_small5 (n - 252) (by omega); rwa [Nat.sub_add_cancel h3] at this
  unfold okB at hok
  rw [List.any_eq_true] at hok
  obtain ⟨a, ha, hd⟩ := hok
  have ha' := List.mem_range.mp ha
  simp only [decide_eq_true_eq] at hd
  exact ⟨a, n - a, by omega, hd.1, by omega, hd.2.1, hd.2.2⟩

theorem B2_1_main (n : ℕ) (hn : 2 ≤ n) : ∃ a b, a + b = n ∧ 0 < a ∧ 0 < b ∧
    σ 1 a < 2 * a ∧ σ 1 b < 2 * b := by
  rcases Nat.lt_or_ge n 300 with h | h
  · exact B2_small n hn h
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ho
  · have := B2_even K (by omega)
    rwa [show 2 * K = n by omega] at this
  · have hn2 : n % 2 = 1 := Nat.odd_iff.mp ho
    by_cases h3 : n % 3 = 2
    · exact B2_odd n 5 hn2 h (Or.inr rfl) (by omega)
    · exact B2_odd n 1 hn2 h (Or.inl rfl) (by omega)
