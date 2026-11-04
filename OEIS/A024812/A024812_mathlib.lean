/-
OEIS A024812, conjecture (L. E. Jeffery 2013): A024812(k) = (A024813(k) + k - 1)/2.
Here f(m) = floor(cot(π/(2m))); A024812 lists the positive values taken by f
for exactly one m ≥ 1, A024813 the m with f(m-1) < f(m) < f(m+1).

Formalisation (`f m = ⌊Real.cot (π / (2m))⌋`).
* `OncePos m`: f(m-1) < f(m) < f(m+1) (the terms of A024813, m ≥ 2).
* `OnceVal n`: there is exactly one i ≥ 1 with f i = n (A024812 when n ≥ 1).
Main theorem `A024812_conjecture`: for every m ≥ 2 with `OncePos m`, put
k₁ = #{j ∈ [2, m] : OncePos j} (so m = A024813(k₁)) and
k₂ = #{n ∈ [1, f m] : OnceVal n} (so f m = A024812(k₂)).  Then k₁ = k₂ and
2·f(m) = m + k₁ − 1, i.e. A024812(k) = (A024813(k) + k − 1)/2.  `onceVal_iff`
shows that the once-values are exactly the values at once-positions.  This is
the README result.

Proof.  With θ = π/(2m) ∈ (0, π/2]: 1/θ − θ/2 ≤ cot θ < 1/θ (from
θ < tan θ, sin θ ≤ θ, cos θ ≥ 1 − θ²/2), so for m ≥ 1: f(m) ≤ f(m+1),
f(m) + 1 ≤ f(m+2), and f(m+1) ≤ f(m) + 1 (m ≥ 3 by the bounds, m = 1, 2 from
f(1) = 0, f(2) = 1, f(3) = ⌊√3⌋ = 1).  Then the invariant
2f(m) − m − k₁(m) + 1 = [f(m+1) = f(m)] (m ≥ 2) follows by induction.

Not checked: nothing outside Lean.
-/
import Mathlib

open Real Finset

noncomputable def g (m : ℕ) : ℝ := Real.cot (π / (2 * m))
noncomputable def f (m : ℕ) : ℤ := ⌊g m⌋

lemma cot_lt_inv {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ π / 2) : Real.cot θ < 1 / θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [Real.cot_eq_cos_div_sin, div_lt_div_iff₀ hs h0]
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h, Real.cos_pi_div_two]; simp [Real.sin_pi_div_two]
  · have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
    have ht := Real.lt_tan h0 h
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc] at ht
    linarith

lemma cot_ge {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ π / 2) : 1 / θ - θ / 2 ≤ Real.cot θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hsle : Real.sin θ ≤ θ := Real.sin_le h0.le
  have hc : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, h1⟩
  have key : (1 - θ ^ 2 / 2) * Real.sin θ ≤ θ * Real.cos θ := by
    rcases le_or_gt 0 (1 - θ ^ 2 / 2) with h | h
    · nlinarith
    · nlinarith
  rw [Real.cot_eq_cos_div_sin, le_div_iff₀ hs]
  have : (1 / θ - θ / 2) * Real.sin θ = ((1 - θ ^ 2 / 2) * Real.sin θ) / θ := by
    field_simp
  rw [this, div_le_iff₀ h0]
  linarith

lemma g_bounds {m : ℕ} (hm : 1 ≤ m) :
    2 * (m : ℝ) / π - π / (4 * m) ≤ g m ∧ g m < 2 * (m : ℝ) / π := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hθ0 : 0 < π / (2 * m) := by positivity
  have hθ1 : π / (2 * m) ≤ π / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num); linarith
  have e1 : 1 / (π / (2 * m)) = 2 * (m : ℝ) / π := by field_simp
  have e2 : π / (2 * m) / 2 = π / (4 * m) := by field_simp; ring
  constructor
  · have := cot_ge hθ0 hθ1; rw [e1, e2] at this; exact this
  · have := cot_lt_inv hθ0 hθ1; rw [e1] at this; exact this

lemma g_mono {m : ℕ} (hm : 1 ≤ m) : g m ≤ g (m + 1) := by
  have h1 := (g_bounds hm).2
  have h2 := (g_bounds (by omega : 1 ≤ m + 1)).1
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hp : 0 < π := Real.pi_pos
  have key : π / (4 * ((m : ℝ) + 1)) ≤ 2 / π := by
    rw [div_le_div_iff₀ (by positivity) hp]; nlinarith
  have e : 2 * ((m + 1 : ℕ) : ℝ) / π = 2 * (m : ℝ) / π + 2 / π := by push_cast; ring
  push_cast at h2
  rw [show 2 * ((m : ℝ) + 1) / π = 2 * (m : ℝ) / π + 2 / π by ring] at h2
  linarith

lemma g_twice {m : ℕ} (hm : 1 ≤ m) : g m + 1 ≤ g (m + 2) := by
  have h1 := (g_bounds hm).2
  have h2 := (g_bounds (by omega : 1 ≤ m + 2)).1
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hp : 0 < π := Real.pi_pos
  have key : 1 + π / (4 * ((m : ℝ) + 2)) ≤ 4 / π := by
    have : π / (4 * ((m : ℝ) + 2)) ≤ 4 / π - 1 := by
      rw [show 4 / π - 1 = (4 - π) / π by field_simp, div_le_div_iff₀ (by positivity) hp]
      nlinarith
    linarith
  push_cast at h2
  rw [show 2 * ((m : ℝ) + 2) / π = 2 * (m : ℝ) / π + 4 / π by ring] at h2
  linarith

lemma g_step {m : ℕ} (hm : 3 ≤ m) : g (m + 1) ≤ g m + 1 := by
  have h1 := (g_bounds (by omega : 1 ≤ m + 1)).2
  have h2 := (g_bounds (by omega : 1 ≤ m)).1
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hp : 0 < π := Real.pi_pos
  have key : 2 / π + π / (4 * (m : ℝ)) ≤ 1 := by
    have : π / (4 * (m : ℝ)) ≤ 1 - 2 / π := by
      rw [show 1 - 2 / π = (π - 2) / π by field_simp, div_le_div_iff₀ (by positivity) hp]
      nlinarith
    linarith
  push_cast at h1
  rw [show 2 * ((m : ℝ) + 1) / π = 2 * (m : ℝ) / π + 2 / π by ring] at h1
  linarith

lemma f_one : f 1 = 0 := by
  simp only [f, g, Nat.cast_one, mul_one]
  rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two]; simp

lemma f_two : f 2 = 1 := by
  simp only [f, g]
  rw [show π / (2 * ((2 : ℕ) : ℝ)) = π / 4 by push_cast; ring, Real.cot_eq_cos_div_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four, div_self (by positivity)]
  simp

lemma f_three : f 3 = 1 := by
  simp only [f, g]
  rw [show π / (2 * ((3 : ℕ) : ℝ)) = π / 6 by push_cast; ring, Real.cot_eq_cos_div_sin,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  rw [Int.floor_eq_iff]
  have h1 : (1 : ℝ) ≤ √3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2 : √3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · push_cast; field_simp; linarith
  · push_cast; field_simp; linarith

lemma f_mono {m : ℕ} (hm : 1 ≤ m) : f m ≤ f (m + 1) := Int.floor_mono (g_mono hm)

lemma f_twice {m : ℕ} (hm : 1 ≤ m) : f m + 1 ≤ f (m + 2) := by
  rw [f, f, ← Int.floor_add_one]; exact Int.floor_mono (g_twice hm)

lemma f_step {m : ℕ} (hm : 1 ≤ m) : f (m + 1) ≤ f m + 1 := by
  rcases Nat.lt_or_ge m 3 with h | h
  · interval_cases m
    · rw [f_two, f_one]; norm_num
    · rw [f_three, f_two]; norm_num
  · rw [f, f, ← Int.floor_add_one]; exact Int.floor_mono (g_step h)

lemma f_mono' {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : f i ≤ f j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact ih.trans (f_mono (by omega))

/-- A024813: positions m with f(m-1) < f(m) < f(m+1). -/
def OncePos (m : ℕ) : Prop := f (m - 1) < f m ∧ f m < f (m + 1)

/-- A024812 (for n ≥ 1): n is taken by f at exactly one m ≥ 1. -/
def OnceVal (n : ℤ) : Prop := ∃ i, 1 ≤ i ∧ f i = n ∧ ∀ j, 1 ≤ j → f j = n → j = i

lemma oncePos_iff {m : ℕ} (hm : 2 ≤ m) : OncePos m ↔ ∀ j, 1 ≤ j → f j = f m → j = m := by
  constructor
  · rintro ⟨h1, h2⟩ j hj hjm
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := f_mono' hj (by omega : j ≤ m - 1); omega
    · have := f_mono' (by omega : 1 ≤ m + 1) (by omega : m + 1 ≤ j); omega
  · intro h
    have a := f_mono (by omega : 1 ≤ m - 1)
    rw [show m - 1 + 1 = m by omega] at a
    have b := f_mono (by omega : 1 ≤ m)
    constructor
    · rcases lt_or_eq_of_le a with h' | h'
      · exact h'
      · have := h (m - 1) (by omega) h'; omega
    · rcases lt_or_eq_of_le b with h' | h'
      · exact h'
      · have := h (m + 1) (by omega) h'.symm; omega

/-- The once-values are exactly the values at once-positions. -/
theorem onceVal_iff (n : ℤ) (hn : 1 ≤ n) : OnceVal n ↔ ∃ m, 2 ≤ m ∧ OncePos m ∧ f m = n := by
  constructor
  · rintro ⟨i, hi, hfi, huniq⟩
    have hi2 : 2 ≤ i := by
      by_contra h; have : i = 1 := by omega
      subst this; rw [f_one] at hfi; omega
    refine ⟨i, hi2, (oncePos_iff hi2).2 (fun j hj hj' => huniq j hj (hj'.trans hfi)), hfi⟩
  · rintro ⟨m, hm2, hm, rfl⟩
    exact ⟨m, by omega, rfl, (oncePos_iff hm2).1 hm⟩

open Classical in
/-- Number of once-positions in [2, m]. -/
noncomputable def K (m : ℕ) : ℤ := ∑ j ∈ Icc 2 m, (if OncePos j then 1 else 0)

open Classical in
lemma invariant (m : ℕ) (hm : 2 ≤ m) :
    2 * f m - m - K m + 1 = (if f (m + 1) = f m then 1 else 0) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h3 : f 3 ≤ f 2 + 1 := f_step (m := 2) (by norm_num)
    have h3' : f 2 ≤ f 3 := f_mono (m := 2) (by norm_num)
    rw [f_two] at h3 h3'
    simp only [K, Icc_self, sum_singleton, OncePos, show (2 : ℕ) - 1 = 1 by rfl,
      show (2 : ℕ) + 1 = 3 by rfl, f_one, f_two]
    split_ifs <;> push_cast <;> omega
  | succ m hm ih =>
    have hK : K (m + 1) = K m + (if OncePos (m + 1) then 1 else 0) := by
      simp only [K]; rw [Finset.sum_Icc_succ_top (by omega)]
    have a : f m ≤ f (m + 1) := f_mono (by omega)
    have b : f (m + 1) ≤ f m + 1 := f_step (by omega)
    have c : f m + 1 ≤ f (m + 2) := f_twice (by omega)
    have d : f (m + 1) ≤ f (m + 2) := f_mono (m := m + 1) (by omega)
    have e : f (m + 2) ≤ f (m + 1) + 1 := f_step (m := m + 1) (by omega)
    rw [hK]
    simp only [OncePos, show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega]
    push_cast
    split_ifs at ih ⊢ <;> omega

open Classical in
/-- The two counts agree: once-positions in [2, m] ↔ once-values in [1, f m]. -/
lemma count_eq (m : ℕ) (hm : 2 ≤ m) (hpos : OncePos m) :
    ((Icc 2 m).filter (fun j => OncePos j)).card =
      ((Icc 1 (f m)).filter (fun n => OnceVal n)).card := by
  classical
  apply Finset.card_bij (fun j _ => f j)
  · intro j hj
    simp only [mem_filter, mem_Icc] at hj ⊢
    refine ⟨⟨?_, f_mono' (by omega) hj.1.2⟩, ?_⟩
    · have := f_mono' (by omega : 1 ≤ 2) hj.1.1; rw [f_two] at this; exact this
    · have h1 : 1 ≤ f j := by
        have := f_mono' (by omega : 1 ≤ 2) hj.1.1; rw [f_two] at this; exact this
      exact (onceVal_iff _ h1).2 ⟨j, hj.1.1, hj.2, rfl⟩
  · intro i hi j hj hij
    simp only [mem_filter, mem_Icc] at hi hj
    exact (oncePos_iff hj.1.1).1 hj.2 i (by omega) hij
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨j, hj2, hjpos, rfl⟩ := (onceVal_iff n hn.1.1).1 hn.2
    refine ⟨j, ?_, rfl⟩
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨hj2, ?_⟩, hjpos⟩
    by_contra hjm
    have := f_mono' (by omega : 1 ≤ m + 1) (by omega : m + 1 ≤ j)
    have := hpos.2
    omega

open Classical in
theorem A024812_conjecture (m : ℕ) (hm : 2 ≤ m) (hpos : OncePos m) :
    let k₁ := ((Icc 2 m).filter (fun j => OncePos j)).card
    let k₂ := ((Icc 1 (f m)).filter (fun n => OnceVal n)).card
    k₁ = k₂ ∧ 2 * f m = m + k₁ - 1 := by
  classical
  intro k₁ k₂
  refine ⟨count_eq m hm hpos, ?_⟩
  have hinv := invariant m hm
  have hne : f (m + 1) ≠ f m := by have := hpos.2; omega
  simp only [hne, ↓reduceIte] at hinv
  have hK : K m = k₁ := by
    simp only [K, k₁]
    rw [Finset.sum_boole]
  rw [hK] at hinv
  linarith
