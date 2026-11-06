import Mathlib

/-!
# OEIS A223577 and A223578: A223578(n) = 2*A223577(n) - n + 1

Checked here (Mathlib, no sorry, no native_decide):
* `f m = ⌊cot (π / (2m))⌋` for integers m (as in both OEIS names);
* `P77 k`: k ≥ 1 and exactly one negative integer m has f m = -k (A223577);
* `P78 k`: k ≥ 2 and f(-k-1) < f(-k) < f(-k+1) (A223578; k = 1 is excluded
  because it would need f(0), which the OEIS definition leaves undefined);
* `A223578_eq`: for every n (0-based), nth P78 n = 2 * nth P77 n - (n+1) + 1,
  i.e. A223578(n) = 2*A223577(n) - n + 1 with OEIS offset 1;
* `A223577_eq`: the equivalent form 2*A223577(n) = A223578(n) + n - 1;
* `P78_infinite`, `P77_infinite`: both sets are infinite, so `Nat.nth` enumerates them.

Not checked here: that `P77`, `P78` transcribe the OEIS names (read by hand;
certificate/check.py compares them with the b-files for n ≤ 10000).
-/

-- The namespace is left open to the end of the file so that the
-- axiom report appended by tools/leancheck-mathlib.sh resolves the names.
--
namespace A223577

open Real Classical

/-- f(m) = ⌊cot(π/(2m))⌋. -/
noncomputable def f (m : ℤ) : ℤ := ⌊Real.cot (π / (2 * (m : ℝ)))⌋

/-- A223577: positive k with exactly one negative m such that -k = f(m). -/
def P77 (k : ℕ) : Prop := 1 ≤ k ∧ ∃! m : ℤ, m < 0 ∧ f m = -(k : ℤ)

/-- A223578: k ≥ 2 with f(-k-1) < f(-k) < f(-k+1). -/
def P78 (k : ℕ) : Prop :=
  2 ≤ k ∧ f (-(k : ℤ) - 1) < f (-(k : ℤ)) ∧ f (-(k : ℤ)) < f (-(k : ℤ) + 1)

/-- c(j) = cot(π/(2j)). -/
noncomputable def c (j : ℕ) : ℝ := Real.cot (π / (2 * (j : ℝ)))

lemma c_one : c 1 = 0 := by
  have h : π / (2 * ((1 : ℕ) : ℝ)) = π / 2 := by push_cast; ring
  rw [c, h, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, zero_div]

lemma c_two : c 2 = 1 := by
  have h : π / (2 * ((2 : ℕ) : ℝ)) = π / 4 := by push_cast; ring
  rw [c, h, Real.cot_eq_cos_div_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  exact div_self (by positivity)

lemma cot_sub (a b : ℝ) (ha : sin a ≠ 0) (hb : sin b ≠ 0) :
    Real.cot a - Real.cot b = sin (b - a) / (sin a * sin b) := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_sub]
  field_simp

-- For j ≥ 2 the step c(j+1) - c(j) lies in [3/5, 1]: write it as
-- sin(b-a)/(sin a sin b) with a = π/(2(j+1)), b = π/(2j), b - a = (2/π) a b,
-- and use x - x³/6 < sin x < x.
--
lemma incr_ge_two (j : ℕ) (hj : 2 ≤ j) : c j + 3 / 5 ≤ c (j + 1) ∧ c (j + 1) ≤ c j + 1 := by
  have hx : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have hc1 : c (j + 1) = Real.cot (π / (2 * ((j : ℝ) + 1))) := by
    simp only [c, Nat.cast_add, Nat.cast_one]
  have hc0 : c j = Real.cot (π / (2 * (j : ℝ))) := rfl
  set x : ℝ := (j : ℝ) with hxdef
  set a := π / (2 * (x + 1)) with ha_def
  set b := π / (2 * x) with hb_def
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 0.79 := by
    rw [hb_def, div_le_iff₀ (by positivity)]; linarith
  have hab : b - a = π / (2 * x * (x + 1)) := by
    rw [ha_def, hb_def]; field_simp; ring
  have hab0 : 0 < b - a := by rw [hab]; positivity
  have hab1 : b - a ≤ 0.27 := by
    have h12 : 12 ≤ 2 * x * (x + 1) := by nlinarith
    rw [hab, div_le_iff₀ (by positivity)]; linarith
  have habq : b - a = a * b * (2 / π) := by
    rw [ha_def, hb_def]; field_simp; ring
  have hsa0 : 0 < sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith)
  have hsb0 : 0 < sin b := Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith)
  have hsa1 : sin a < a := Real.sin_lt ha0
  have hsb1 : sin b < b := Real.sin_lt hb0
  have hs1 : sin (b - a) < b - a := Real.sin_lt hab0
  have hsa2 := Real.sin_gt_sub_cube ha0
  have hsb2 := Real.sin_gt_sub_cube hb0
  have hs2 := Real.sin_gt_sub_cube hab0
  have hq1 : 2 / π < 0.64 := by rw [div_lt_iff₀ hpi0]; linarith
  have hq2 : 0.63 < 2 / π := by rw [lt_div_iff₀ hpi0]; linarith
  have hd : c (j + 1) - c j = sin (b - a) / (sin a * sin b) := by
    rw [hc1, hc0]; exact cot_sub a b hsa0.ne' hsb0.ne'
  have hab_lt : a < b := by linarith
  -- lower bounds on sin a, sin b and sin (b - a)
  --
  have hla : 0.89 * a ≤ sin a := by
    have : a ^ 3 / 6 ≤ 0.11 * a := by
      have h2 : a ^ 2 ≤ 0.66 := by nlinarith
      have h3 : a ^ 3 = a * a ^ 2 := by ring
      have h4 := mul_le_mul_of_nonneg_left h2 ha0.le
      linarith
    linarith
  have hlb : 0.89 * b ≤ sin b := by
    have : b ^ 3 / 6 ≤ 0.11 * b := by
      have h2 : b ^ 2 ≤ 0.66 := by nlinarith
      have h3 : b ^ 3 = b * b ^ 2 := by ring
      have h4 := mul_le_mul_of_nonneg_left h2 hb0.le
      linarith
    linarith
  have hls : 0.98 * (b - a) ≤ sin (b - a) := by
    have : (b - a) ^ 3 / 6 ≤ 0.02 * (b - a) := by
      have h2 : (b - a) ^ 2 ≤ 0.12 := by nlinarith
      have h3 : (b - a) ^ 3 = (b - a) * (b - a) ^ 2 := by ring
      have h4 := mul_le_mul_of_nonneg_left h2 hab0.le
      linarith
    linarith
  have hab_pos : 0 < a * b := by positivity
  have hprod_lo : 0.89 * a * (0.89 * b) ≤ sin a * sin b :=
    mul_le_mul hla hlb (by positivity) hsa0.le
  have hprod_hi : sin a * sin b ≤ a * b :=
    mul_le_mul hsa1.le hsb1.le hsb0.le ha0.le
  have hden : 0 < sin a * sin b := by positivity
  constructor
  · have : 3 / 5 ≤ sin (b - a) / (sin a * sin b) := by
      rw [le_div_iff₀ hden]
      have h1 : 3 / 5 * (sin a * sin b) ≤ 3 / 5 * (a * b) := by linarith
      have h2 : 3 / 5 * (a * b) ≤ 0.98 * (b - a) := by
        have h4 := mul_lt_mul_of_pos_left hq2 hab_pos
        rw [habq]; linarith
      linarith
    linarith
  · have : sin (b - a) / (sin a * sin b) ≤ 1 := by
      rw [div_le_iff₀ hden]
      have h1 : b - a ≤ 0.64 * (a * b) := by
        have h4 := mul_lt_mul_of_pos_left hq1 hab_pos
        rw [habq]; linarith
      have h3 : 0.64 * (a * b) ≤ sin a * sin b := by linarith
      linarith
    linarith

lemma incr (j : ℕ) (hj : 1 ≤ j) : c j + 3 / 5 ≤ c (j + 1) ∧ c (j + 1) ≤ c j + 1 := by
  rcases Nat.lt_or_ge j 2 with h | h
  · have : j = 1 := by omega
    subst this
    show c 1 + 3 / 5 ≤ c 2 ∧ c 2 ≤ c 1 + 1
    rw [c_one, c_two]; norm_num
  · exact incr_ge_two j h

lemma c_lower (j : ℕ) (hj : 1 ≤ j) : 3 / 5 * ((j : ℝ) - 1) ≤ c j := by
  induction j, hj using Nat.le_induction with
  | base => rw [c_one]; norm_num
  | succ k hk ih =>
    have := (incr k hk).1
    push_cast
    linarith

lemma c_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ c j := by
  have h := c_lower j hj
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

/-- g(j) = ⌈c(j)⌉ as a natural number. -/
noncomputable def g (j : ℕ) : ℕ := (⌈c j⌉).toNat

lemma gZ (j : ℕ) (hj : 1 ≤ j) : (g j : ℤ) = ⌈c j⌉ :=
  Int.toNat_of_nonneg (Int.ceil_nonneg (c_nonneg j hj))

lemma g_one : g 1 = 0 := by simp [g, c_one]

lemma g_two : g 2 = 1 := by simp [g, c_two]

lemma f_neg (j : ℕ) (hj : 1 ≤ j) : f (-(j : ℤ)) = -(g j : ℤ) := by
  rw [gZ j hj, f, ← Int.floor_neg]
  congr 1
  have h1 : π / (2 * (((-(j : ℤ)) : ℤ) : ℝ)) = -(π / (2 * (j : ℝ))) := by
    push_cast; rw [mul_neg, div_neg]
  rw [h1, c, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg,
    div_neg]

lemma g_step (j : ℕ) (hj : 1 ≤ j) : g j ≤ g (j + 1) ∧ g (j + 1) ≤ g j + 1 := by
  have h := incr j hj
  have e0 := gZ j hj
  have e1 := gZ (j + 1) (by omega)
  have a1 : ⌈c j⌉ ≤ ⌈c (j + 1)⌉ := Int.ceil_mono (by linarith)
  have a2 : ⌈c (j + 1)⌉ ≤ ⌈c j⌉ + 1 := by
    rw [← Int.ceil_add_one]; exact Int.ceil_mono h.2
  omega

lemma g_two_step (j : ℕ) (hj : 1 ≤ j) : g j + 1 ≤ g (j + 2) := by
  have h1 := incr j hj
  have h2 : c (j + 1) + 3 / 5 ≤ c (j + 2) ∧ c (j + 2) ≤ c (j + 1) + 1 := incr (j + 1) (by omega)
  have e0 := gZ j hj
  have e2 := gZ (j + 2) (by omega)
  have a : ⌈c j⌉ + 1 ≤ ⌈c (j + 2)⌉ := by
    rw [← Int.ceil_add_one]; exact Int.ceil_mono (by linarith)
  omega

lemma g_mono {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) : g i ≤ g k := by
  induction k, hik using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (g_step k (by omega)).1

lemma P78_iff (i : ℕ) (hi : 1 ≤ i) :
    P78 (i + 1) ↔ g i < g (i + 1) ∧ g (i + 1) < g (i + 2) := by
  have e1 : -(((i + 1 : ℕ) : ℤ)) - 1 = -(((i + 2 : ℕ) : ℤ)) := by push_cast; ring
  have e2 : -(((i + 1 : ℕ) : ℤ)) + 1 = -((i : ℕ) : ℤ) := by push_cast; ring
  unfold P78
  rw [e1, e2, f_neg (i + 2) (by omega), f_neg (i + 1) (by omega), f_neg i hi]
  constructor
  · rintro ⟨-, h1, h2⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega, by omega⟩

-- A negative integer m is -i with i = (-m).toNat ≥ 1.
--
lemma neg_cases (m : ℤ) (hm : m < 0) : ∃ i : ℕ, 1 ≤ i ∧ m = -(i : ℤ) :=
  ⟨(-m).toNat, by omega, by omega⟩

lemma P77_of (j : ℕ) (hj : 1 ≤ j) (h1 : g (j + 1) = g j + 1) (h2 : g (j + 2) ≠ g (j + 1)) :
    P77 (g (j + 1)) := by
  refine ⟨by omega, -(((j + 1 : ℕ)) : ℤ), ⟨by omega, f_neg (j + 1) (by omega)⟩, ?_⟩
  rintro m ⟨hm, hfm⟩
  obtain ⟨i, hi, rfl⟩ := neg_cases m hm
  rw [f_neg i hi] at hfm
  have hgi : g i = g (j + 1) := by omega
  have s2 : g (j + 1) ≤ g (j + 2) ∧ g (j + 2) ≤ g (j + 1) + 1 := g_step (j + 1) (by omega)
  rcases Nat.lt_or_ge i (j + 1) with h | h
  · have := g_mono hi (show i ≤ j by omega); omega
  · rcases Nat.lt_or_ge (j + 1) i with h' | h'
    · have := g_mono (show 1 ≤ j + 2 by omega) (show j + 2 ≤ i by omega); omega
    · have : i = j + 1 := by omega
      subst this; rfl

lemma not_P77_of (j : ℕ) (h2 : g (j + 2) = g (j + 1)) : ¬ P77 (g (j + 1)) := by
  rintro ⟨-, m, -, huniq⟩
  have a1 := huniq (-(((j + 1 : ℕ)) : ℤ)) ⟨by omega, f_neg (j + 1) (by omega)⟩
  have a2 := huniq (-(((j + 2 : ℕ)) : ℤ)) ⟨by omega, by rw [f_neg (j + 2) (by omega), h2]⟩
  omega

lemma not_P78_small (k : ℕ) (hk : k < 2) : ¬ P78 k := fun h => by have := h.1; omega

lemma not_P77_zero : ¬ P77 0 := fun h => by have := h.1; omega

lemma count78_two : Nat.count P78 2 = 0 :=
  Nat.count_iff_forall_not.2 (fun m hm => not_P78_small m hm)

/-- Counting invariant: count P78 (j+1) + j + [g(j+1) = g(j)] = 2 g(j) + 1. -/
lemma inv1 (j : ℕ) (hj : 1 ≤ j) :
    Nat.count P78 (j + 1) + j + (if g (j + 1) = g j then 1 else 0) = 2 * g j + 1 := by
  induction j, hj using Nat.le_induction with
  | base =>
    show Nat.count P78 2 + 1 + (if g 2 = g 1 then 1 else 0) = 2 * g 1 + 1
    rw [count78_two, g_one, g_two]; simp
  | succ k hk ih =>
    have s1 : g k ≤ g (k + 1) ∧ g (k + 1) ≤ g k + 1 := g_step k hk
    have s2 : g (k + 1) ≤ g (k + 2) ∧ g (k + 2) ≤ g (k + 1) + 1 := g_step (k + 1) (by omega)
    have s3 := g_two_step k hk
    have hP := P78_iff k hk
    have hcs : Nat.count P78 (k + 2) = Nat.count P78 (k + 1) + if P78 (k + 1) then 1 else 0 :=
      Nat.count_succ _ _
    show Nat.count P78 (k + 2) + (k + 1) + (if g (k + 2) = g (k + 1) then 1 else 0) =
      2 * g (k + 1) + 1
    rw [hcs]
    by_cases h : P78 (k + 1)
    · rw [ite_eq_left h]
      have := hP.1 h
      split_ifs at ih ⊢ <;> omega
    · rw [ite_eq_right h]
      have : ¬ (g k < g (k + 1) ∧ g (k + 1) < g (k + 2)) := fun h' => h (hP.2 h')
      split_ifs at ih ⊢ <;> omega

/-- The values g(i) with a unique preimage, counted below g(j)+1, match the
    P78 points up to j. -/
lemma inv2 (j : ℕ) (hj : 1 ≤ j) : Nat.count P77 (g j + 1) = Nat.count P78 (j + 1) := by
  induction j, hj using Nat.le_induction with
  | base =>
    show Nat.count P77 (g 1 + 1) = Nat.count P78 2
    rw [count78_two, g_one, Nat.count_succ, Nat.count_zero, ite_eq_right not_P77_zero]
  | succ k hk ih =>
    have s1 : g k ≤ g (k + 1) ∧ g (k + 1) ≤ g k + 1 := g_step k hk
    have s2 : g (k + 1) ≤ g (k + 2) ∧ g (k + 2) ≤ g (k + 1) + 1 := g_step (k + 1) (by omega)
    have s3 := g_two_step k hk
    have hP := P78_iff k hk
    have hcs : Nat.count P78 (k + 2) = Nat.count P78 (k + 1) + if P78 (k + 1) then 1 else 0 :=
      Nat.count_succ _ _
    show Nat.count P77 (g (k + 1) + 1) = Nat.count P78 (k + 2)
    rw [hcs]
    rcases Nat.eq_or_lt_of_le s1.1 with heq | hlt
    · have hn : ¬ P78 (k + 1) := fun h => by have := hP.1 h; omega
      rw [ite_eq_right hn, ← heq, ih]
      omega
    · have hk1 : g (k + 1) = g k + 1 := by omega
      rw [hk1, Nat.count_succ P77 (g k + 1), ih, ← hk1]
      by_cases h2 : g (k + 2) = g (k + 1)
      · have hn : ¬ P78 (k + 1) := fun h => by have := hP.1 h; omega
        rw [ite_eq_right (not_P77_of k h2), ite_eq_right hn]
      · have hy : P78 (k + 1) := hP.2 ⟨by omega, by omega⟩
        rw [ite_eq_left (P77_of k hk hk1 h2), ite_eq_left hy]

lemma g_lower (j : ℕ) (hj : 1 ≤ j) : 6 * (j : ℤ) - 6 ≤ 10 * (g j : ℤ) := by
  have h1 := c_lower j hj
  have h2 : c j ≤ (g j : ℝ) := by
    have := gZ j hj
    have h3 : c j ≤ (⌈c j⌉ : ℝ) := Int.le_ceil _
    have h4 : ((g j : ℤ) : ℝ) = (⌈c j⌉ : ℝ) := by exact_mod_cast this
    push_cast at h4; linarith
  have : 6 * (j : ℝ) - 6 ≤ 10 * (g j : ℝ) := by linarith
  exact_mod_cast this

theorem P78_infinite : (Set.ofPred P78).Infinite := by
  intro hfin
  have hle := Nat.count_le_card hfin (5 * hfin.toFinset.card + 11 + 1)
  have I := inv1 (5 * hfin.toFinset.card + 11) (by omega)
  have G := g_lower (5 * hfin.toFinset.card + 11) (by omega)
  split_ifs at I <;> omega

theorem P77_infinite : (Set.ofPred P77).Infinite := by
  intro hfin
  have hle : ∀ n, Nat.count P78 n ≤ (hfin.toFinset).card + 2 := by
    intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · have := Nat.count_le (p := P78) (n := n); omega
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      rw [← inv2 j (by omega)]
      exact (Nat.count_le_card hfin _).trans (by omega)
  have h := Nat.count_nth_of_infinite P78_infinite ((hfin.toFinset).card + 3)
  have := hle (Nat.nth P78 ((hfin.toFinset).card + 3))
  omega

/-- A223578(n) = 2*A223577(n) - n + 1 (0-based n here; OEIS index n+1). -/
theorem A223578_eq (n : ℕ) :
    (Nat.nth P78 n : ℤ) = 2 * (Nat.nth P77 n : ℤ) - ((n + 1 : ℕ) : ℤ) + 1 := by
  have hj : P78 (Nat.nth P78 n) := Nat.nth_mem_of_infinite P78_infinite n
  have hc : Nat.count P78 (Nat.nth P78 n) = n := Nat.count_nth_of_infinite P78_infinite n
  obtain ⟨j, hjeq⟩ : ∃ j, Nat.nth P78 n = j + 1 := ⟨Nat.nth P78 n - 1, by have := hj.1; omega⟩
  rw [hjeq] at hj hc ⊢
  have hj1 : 1 ≤ j := by have := hj.1; omega
  have hP := (P78_iff j hj1).1 hj
  have s1 := g_step j hj1
  have hP' : g (j + 1) < g (j + 1 + 1) := hP.2
  have h77 : P77 (g (j + 1)) := P77_of j hj1 (by omega) (by omega)
  have I1 := inv1 (j + 1) (by omega)
  have I2 := inv2 (j + 1) (by omega)
  rw [Nat.count_succ P78 (j + 1), ite_eq_left hj, hc] at I1 I2
  rw [ite_eq_right (show ¬ (g (j + 1 + 1) = g (j + 1)) by omega)] at I1
  rw [Nat.count_succ P77 (g (j + 1)), ite_eq_left h77] at I2
  have hc77 : Nat.count P77 (g (j + 1)) = n := by omega
  have hn : Nat.nth P77 n = g (j + 1) := by rw [← hc77]; exact Nat.nth_count h77
  rw [hn]
  push_cast
  omega

/-- Equivalent form 2*A223577(n) = A223578(n) + n - 1 (0-based n; OEIS index n+1). -/
theorem A223577_eq (n : ℕ) :
    2 * (Nat.nth P77 n : ℤ) = (Nat.nth P78 n : ℤ) + ((n + 1 : ℕ) : ℤ) - 1 := by
  have := A223578_eq n
  omega
