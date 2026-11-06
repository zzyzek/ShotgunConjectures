/-
OEIS A170941: a(n+1) = a(n) + n*a(n-1) - a(n-2) + a(n-3), a(0..3) = 1, 1, 1, 2.
Conjecture (David Callan, entry text): a(n)/A000085(n) -> 1/e.

Definitions.
* `inv n` is A000085 (involutions of [n]): inv 0 = inv 1 = 1,
  inv (n+2) = inv (n+1) + (n+1) * inv n.
* `a n` is A170941 by the entry's recurrence (over ℤ).
* `t n k = (-1)^k * C(n-k, k) * inv (n-2k)` and `b n = Σ_{k ≤ n} t n k`
  (inclusion-exclusion over sets of k disjoint adjacent transpositions).

Main theorems.
* `a_eq_b`: a n = b n for all n (via `b_rec4`, the A170941 recurrence for b).
* `desc_bound`: (n-k)(n-k-1)...(n-2k+1) * inv (n-2k) ≤ inv n.
* `E_tendsto`: for fixed k, (n-k)_k * inv (n-2k) / inv n -> 1.
* `A170941_tendsto`: (a n : ℝ) / inv n -> exp (-1)  (Tannery's theorem).

Not checked in this file: that b n counts involutions of [n] with no
adjacent transposition (i i+1) (the inclusion-exclusion step, Callan's
comment); the proof here is about the sequence defined by the recurrence.
-/
import Mathlib

open Finset Filter Topology

namespace A170941

/-- A000085: number of involutions of [n]. -/
def inv : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => inv (n + 1) + (n + 1) * inv n

/-- A170941 by the recurrence of the entry. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | (n + 4) => a (n + 3) + ((n : ℤ) + 3) * a (n + 2) - a (n + 1) + a n

/-- Inclusion-exclusion term. -/
def t (n k : ℕ) : ℤ := (-1) ^ k * (((n - k).choose k : ℕ) : ℤ) * ((inv (n - 2 * k) : ℕ) : ℤ)

def b (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), t n k

def K (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (k : ℤ) * t n k

/-- Shifted part of Pascal's rule, used in `b_term`. -/
def s (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | (k + 1) => - t n k

theorem inv_succ_succ (n : ℕ) : inv (n + 2) = inv (n + 1) + (n + 1) * inv n := rfl

theorem inv_pos : ∀ n, 0 < inv n
  | 0 => by decide
  | 1 => by decide
  | (n + 2) => by
    rw [inv_succ_succ]
    have := inv_pos (n + 1)
    omega

theorem t_eq_zero {n k : ℕ} (h : n < 2 * k) : t n k = 0 := by
  unfold t
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem t_eval (n k r : ℕ) (h : n = 2 * k + r) :
    t n k = (-1) ^ k * (((k + r).choose k : ℕ) : ℤ) * ((inv r : ℕ) : ℤ) := by
  unfold t
  have e1 : n - k = k + r := by omega
  have e2 : n - 2 * k = r := by omega
  rw [e1, e2]

theorem sum_extend (n M : ℕ) (f : ℕ → ℤ) (hf : ∀ k, n < 2 * k → f k = 0) (hM : n + 1 ≤ M) :
    ∑ k ∈ range M, f k = ∑ k ∈ range (n + 1), f k := by
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_range, not_lt] at hx hx'
    exact hf x (by omega)

theorem K_term (m k : ℕ) :
    ((k : ℤ) + 1) * t (m + 2) (k + 1) = ((k : ℤ) - ((m : ℤ) + 1)) * t m k := by
  rcases Nat.lt_or_ge m (2 * k) with h | h
  · rw [t_eq_zero h, t_eq_zero (by omega)]
    ring
  · obtain ⟨r, rfl⟩ : ∃ r, m = 2 * k + r := ⟨m - 2 * k, by omega⟩
    rw [t_eval (2 * k + r + 2) (k + 1) r (by omega), t_eval (2 * k + r) k r rfl]
    have hc := Nat.add_one_mul_choose_eq (k + r) k
    have e : k + 1 + r = k + r + 1 := by omega
    rw [e]
    have hc' : ((k : ℤ) + r + 1) * (((k + r).choose k : ℕ) : ℤ) =
        (((k + r + 1).choose (k + 1) : ℕ) : ℤ) * ((k : ℤ) + 1) := by
      exact_mod_cast hc
    push_cast
    linear_combination ((-1 : ℤ) ^ k * ((inv r : ℕ) : ℤ)) * hc'

theorem K_rec (m : ℕ) : K (m + 2) = K m - ((m : ℤ) + 1) * b m := by
  have h1 : K (m + 2) = ∑ k ∈ range (m + 2), ((k : ℤ) - ((m : ℤ) + 1)) * t m k := by
    unfold K
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [← K_term]
    push_cast
    ring
  have h2 : ∑ k ∈ range (m + 2), ((k : ℤ) - ((m : ℤ) + 1)) * t m k =
      ∑ k ∈ range (m + 1), ((k : ℤ) - ((m : ℤ) + 1)) * t m k :=
    sum_extend m (m + 2) _ (fun k hk => by rw [t_eq_zero hk]; ring) (by omega)
  rw [h1, h2]
  unfold K b
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem b_term (n k : ℕ) :
    t (n + 2) k = t (n + 1) k + ((n : ℤ) + 1 - k) * t n k + s n k := by
  rcases k with _ | j
  · rw [t_eval (n + 2) 0 (n + 2) (by omega), t_eval (n + 1) 0 (n + 1) (by omega),
      t_eval n 0 n (by omega), inv_succ_succ]
    simp only [s, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.cast_zero]
    push_cast
    ring
  · simp only [s]
    rcases Nat.lt_or_ge n (2 * j) with h | h
    · rw [t_eq_zero (n := n + 2) (by omega), t_eq_zero (n := n + 1) (by omega),
        t_eq_zero (n := n) (k := j + 1) (by omega), t_eq_zero h]
      ring
    rcases Nat.lt_or_ge n (2 * j + 2) with h' | h'
    · rcases (show n = 2 * j ∨ n = 2 * j + 1 by omega) with rfl | rfl
      · rw [t_eval (2 * j + 2) (j + 1) 0 (by omega), t_eq_zero (n := 2 * j + 1) (by omega),
          t_eq_zero (n := 2 * j) (k := j + 1) (by omega), t_eval (2 * j) j 0 (by omega)]
        simp only [add_zero, Nat.choose_self, inv, Nat.cast_one]
        ring
      · rw [t_eval (2 * j + 1 + 2) (j + 1) 1 (by omega), t_eval (2 * j + 1 + 1) (j + 1) 0 (by omega),
          t_eq_zero (n := 2 * j + 1) (k := j + 1) (by omega), t_eval (2 * j + 1) j 1 (by omega)]
        simp only [add_zero, Nat.choose_self, Nat.choose_succ_self_right, inv, Nat.cast_one]
        push_cast
        ring
    · obtain ⟨r, rfl⟩ : ∃ r, n = 2 * j + 2 + r := ⟨n - (2 * j + 2), by omega⟩
      rw [t_eval (2 * j + 2 + r + 2) (j + 1) (r + 2) (by omega),
        t_eval (2 * j + 2 + r + 1) (j + 1) (r + 1) (by omega),
        t_eval (2 * j + 2 + r) (j + 1) r (by omega),
        t_eval (2 * j + 2 + r) j (r + 2) (by omega), inv_succ_succ r]
      have hp := Nat.choose_succ_succ' (j + 2 + r) j
      have hm := Nat.choose_mul_succ_eq (j + 1 + r) (j + 1)
      have e1 : j + 1 + (r + 2) = j + 2 + r + 1 := by omega
      have e2 : j + 1 + (r + 1) = j + 2 + r := by omega
      have e3 : j + 1 + r + 1 = j + 2 + r := by omega
      have e4 : j + 2 + r - (j + 1) = r + 1 := by omega
      have e5 : j + (r + 2) = j + 2 + r := by omega
      have e6 : j + 1 + r = j + 1 + r := rfl
      rw [e3, e4] at hm
      rw [e1, e2, e5]
      have hp' : (((j + 2 + r + 1).choose (j + 1) : ℕ) : ℤ) =
          (((j + 2 + r).choose j : ℕ) : ℤ) + (((j + 2 + r).choose (j + 1) : ℕ) : ℤ) := by
        exact_mod_cast hp
      have hm' : (((j + 1 + r).choose (j + 1) : ℕ) : ℤ) * ((j : ℤ) + 2 + r) =
          (((j + 2 + r).choose (j + 1) : ℕ) : ℤ) * ((r : ℤ) + 1) := by
        exact_mod_cast hm
      clear e6
      rw [hp']
      push_cast
      linear_combination ((-1 : ℤ) ^ j * ((inv r : ℕ) : ℤ)) * hm'

theorem b_rec2 (n : ℕ) : b (n + 2) = b (n + 1) + (n : ℤ) * b n - K n := by
  have h1 : b (n + 2) = ∑ k ∈ range (n + 2 + 1),
      (t (n + 1) k + ((n : ℤ) + 1 - k) * t n k + s n k) := by
    unfold b
    apply Finset.sum_congr rfl
    intro k _
    exact b_term n k
  rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs : ∑ k ∈ range (n + 2 + 1), s n k = - b n := by
    rw [Finset.sum_range_succ']
    simp only [s, add_zero]
    rw [Finset.sum_neg_distrib]
    unfold b
    rw [sum_extend n (n + 2) _ (fun k hk => t_eq_zero hk) (by omega)]
  have ht1 : ∑ k ∈ range (n + 2 + 1), t (n + 1) k = b (n + 1) := by
    unfold b
    exact sum_extend (n + 1) (n + 2 + 1) _ (fun k hk => t_eq_zero hk) (by omega)
  have ht2 : ∑ k ∈ range (n + 2 + 1), ((n : ℤ) + 1 - k) * t n k = ((n : ℤ) + 1) * b n - K n := by
    rw [sum_extend n (n + 2 + 1) _ (fun k hk => by rw [t_eq_zero hk]; ring) (by omega)]
    unfold b K
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs, ht1, ht2]
  ring

theorem b_rec4 (n : ℕ) :
    b (n + 4) = b (n + 3) + ((n : ℤ) + 3) * b (n + 2) - b (n + 1) + b n := by
  have h1 : b (n + 4) = b (n + 3) + ((n : ℤ) + 2) * b (n + 2) - K (n + 2) := by
    have := b_rec2 (n + 2)
    push_cast at this
    exact this
  have h2 := K_rec n
  have h3 := b_rec2 n
  linear_combination h1 - h2 - h3

theorem a_eq_b : ∀ n, a n = b n
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | (n + 4) => by
    rw [b_rec4, ← a_eq_b (n + 3), ← a_eq_b (n + 2), ← a_eq_b (n + 1), ← a_eq_b n]
    rfl

/-! Analysis. -/

/-- (n+1) inv(n)^2 ≤ inv(n+1)^2, in pairs for the two-step induction. -/
theorem inv_lower_aux : ∀ n, (n + 1) * inv n ^ 2 ≤ inv (n + 1) ^ 2 ∧
    (n + 2) * inv (n + 1) ^ 2 ≤ inv (n + 2) ^ 2
  | 0 => by decide
  | (n + 1) => by
    refine ⟨(inv_lower_aux n).2, ?_⟩
    have h := (inv_lower_aux n).1
    have e : inv (n + 1 + 2) = inv (n + 2) + (n + 2) * inv (n + 1) := rfl
    rw [e, inv_succ_succ n]
    have h2 := Nat.mul_le_mul_left ((n + 2) * (n + 1)) h
    nlinarith [h2, Nat.zero_le (inv (n + 1)), Nat.zero_le (inv n)]

theorem inv_lower (n : ℕ) : (n + 1) * inv n ^ 2 ≤ inv (n + 1) ^ 2 := (inv_lower_aux n).1

theorem inv_upper (n : ℕ) : (inv (n + 1) : ℝ) ^ 2 ≤ 2 * ((n : ℝ) + 1) * (inv n : ℝ) ^ 2 := by
  rcases n with _ | m
  · norm_num [inv]
  · have hL : ((m : ℝ) + 1) * (inv m : ℝ) ^ 2 ≤ (inv (m + 1) : ℝ) ^ 2 := by
      exact_mod_cast inv_lower m
    rw [inv_succ_succ]
    push_cast
    have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    nlinarith [sq_nonneg ((inv (m + 1) : ℝ) - ((m : ℝ) + 1) * inv m),
      mul_le_mul_of_nonneg_left hL hm]

theorem desc_bound : ∀ k n : ℕ, (n - k).descFactorial k * inv (n - 2 * k) ≤ inv n := by
  intro k
  induction k with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    rcases Nat.lt_or_ge n (2 * k + 2) with h | h
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have e1 : m + 2 - (k + 1) = (m - k) + 1 := by omega
      have e2 : m + 2 - 2 * (k + 1) = m - 2 * k := by omega
      rw [e1, e2, Nat.succ_descFactorial_succ, inv_succ_succ]
      calc (m - k + 1) * (m - k).descFactorial k * inv (m - 2 * k)
          = (m - k + 1) * ((m - k).descFactorial k * inv (m - 2 * k)) := by ring
        _ ≤ (m + 1) * inv m := Nat.mul_le_mul (by omega) (ih m)
        _ ≤ inv (m + 1) + (m + 1) * inv m := Nat.le_add_left _ _

/-- I(n+1) / ((n+1) I(n)). -/
noncomputable def q (m : ℕ) : ℝ := (inv (m + 1) : ℝ) / (((m : ℝ) + 1) * inv m)

theorem q_nonneg (m : ℕ) : 0 ≤ q m := by
  unfold q
  positivity

theorem q_sq_le (m : ℕ) : q m ^ 2 ≤ 2 * (1 / ((m : ℝ) + 1)) := by
  have hi : (0 : ℝ) < inv m := by exact_mod_cast inv_pos m
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  unfold q
  rw [div_pow, mul_one_div, div_le_div_iff₀ (by positivity) hm]
  nlinarith [mul_le_mul_of_nonneg_right (inv_upper m) hm.le]

theorem q_tendsto : Tendsto q atTop (𝓝 0) := by
  have h0 : Tendsto (fun m : ℕ => 2 * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  have h1 : Tendsto (fun m : ℕ => Real.sqrt (2 * (1 / ((m : ℝ) + 1)))) atTop (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at h2
    exact h2
  refine squeeze_zero q_nonneg (fun m => ?_) h1
  rw [← Real.sqrt_sq (q_nonneg m)]
  exact Real.sqrt_le_sqrt (q_sq_le m)

theorem ratio_tendsto (k : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 1 - k) * inv m / inv (m + 2)) atTop (𝓝 1) := by
  have hk : Tendsto (fun m : ℕ => 1 - (k : ℝ) * (1 / ((m : ℝ) + 1))) atTop (𝓝 (1 - k * 0)) :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (k : ℝ)).const_sub 1
  have hq : Tendsto (fun m => 1 + q m) atTop (𝓝 (1 + 0)) := q_tendsto.const_add 1
  have h := hk.div hq (by norm_num)
  simp only [mul_zero, sub_zero, add_zero, div_one] at h
  refine h.congr (fun m => ?_)
  have hi : (0 : ℝ) < inv m := by exact_mod_cast inv_pos m
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have e : (inv (m + 2) : ℝ) = inv (m + 1) + ((m : ℝ) + 1) * inv m := by
    rw [inv_succ_succ]
    push_cast
    ring
  simp only [Pi.div_apply]
  rw [e]
  unfold q
  field_simp
  ring

/-- (n-k)_k I(n-2k) / I(n). -/
noncomputable def E (n k : ℕ) : ℝ := ((n - k).descFactorial k : ℝ) * inv (n - 2 * k) / inv n

theorem E_tendsto (k : ℕ) : Tendsto (fun n => E n k) atTop (𝓝 1) := by
  induction k with
  | zero =>
    refine tendsto_const_nhds.congr (fun n => ?_)
    have hi : (0 : ℝ) < inv n := by exact_mod_cast inv_pos n
    unfold E
    simp only [Nat.sub_zero, Nat.descFactorial_zero, Nat.cast_one, one_mul, mul_zero]
    rw [div_self hi.ne']
  | succ k ih =>
    rw [← tendsto_add_atTop_iff_nat 2]
    have h := ih.mul (ratio_tendsto k)
    rw [mul_one] at h
    refine h.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    refine ⟨k, fun n hn => ?_⟩
    have hi : (0 : ℝ) < inv n := by exact_mod_cast inv_pos n
    have hi2 : (0 : ℝ) < inv (n + 2) := by exact_mod_cast inv_pos (n + 2)
    have e1 : n + 2 - (k + 1) = (n - k) + 1 := by omega
    have e2 : n + 2 - 2 * (k + 1) = n - 2 * k := by omega
    unfold E
    rw [e1, e2, Nat.succ_descFactorial_succ]
    push_cast [Nat.cast_sub hn]
    field_simp
    ring

/-- Normalised term of the inclusion-exclusion sum. -/
noncomputable def f (n k : ℕ) : ℝ := (-1) ^ k / (k.factorial : ℝ) * E n k

theorem t_div (n k : ℕ) : (t n k : ℝ) / inv n = f n k := by
  have hi : (0 : ℝ) < inv n := by exact_mod_cast inv_pos n
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  unfold t f E
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

theorem f_eq_zero {n k : ℕ} (h : n + 1 ≤ k) : f n k = 0 := by
  unfold f E
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
  simp

theorem E_le_one (n k : ℕ) : 0 ≤ E n k ∧ E n k ≤ 1 := by
  have hi : (0 : ℝ) < inv n := by exact_mod_cast inv_pos n
  refine ⟨by unfold E; positivity, ?_⟩
  unfold E
  rw [div_le_one hi]
  exact_mod_cast desc_bound k n

theorem A170941_tendsto :
    Tendsto (fun n => (a n : ℝ) / inv n) atTop (𝓝 (Real.exp (-1))) := by
  have hsum : HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (k.factorial : ℝ)) (Real.exp (-1)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)
  have hbound : Summable (fun k : ℕ => 1 / (k.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  have hT := tendsto_tsum_of_dominated_convergence (f := f)
    (g := fun k : ℕ => (-1 : ℝ) ^ k / (k.factorial : ℝ)) (𝓕 := atTop) hbound
    (fun k => by simpa [f] using (E_tendsto k).const_mul ((-1 : ℝ) ^ k / (k.factorial : ℝ)))
    (Eventually.of_forall (fun n k => by
      have hE := E_le_one n k
      have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
      unfold f
      rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg hE.1,
        Real.norm_of_nonneg hf.le]
      calc 1 / (k.factorial : ℝ) * E n k ≤ 1 / (k.factorial : ℝ) * 1 := by
            gcongr
            exact hE.2
        _ = 1 / (k.factorial : ℝ) := mul_one _))
  rw [hsum.tsum_eq] at hT
  refine hT.congr (fun n => ?_)
  rw [tsum_eq_sum (s := range (n + 1)) (fun k hk => by
    simp only [Finset.mem_range, not_lt] at hk
    exact f_eq_zero hk)]
  rw [a_eq_b, b]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _ => (t_div n k).symm)

