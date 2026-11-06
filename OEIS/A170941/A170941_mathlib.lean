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

Combinatorial definition (Callan's comment).
* `A170941count n` = number of σ : Equiv.Perm (Fin n) with σ * σ = 1 and no
  i with σ i = i + 1 (no adjacent transposition).
* `count_gen`: involutions of Fin m with prescribed values on a set D
  (closed under an involution p) number inv (m - |D|); proved by splitting
  on the image of the last point (`invol_split`).
* `count_adj`: involutions containing the transpositions (i i+1), i ∈ K,
  number inv (n - 2|K|) if K is a set of pairwise non-consecutive
  i < n - 1 (`Good n K`), else 0.
* `ie_count`: inclusion-exclusion over K; `Sg_eq_Bg`: the number of good K
  of size k is C(n-k, k).
* `A170941count_eq`: (A170941count n : ℤ) = a n.
* `A170941count_tendsto`: (A170941count n : ℝ) / inv n -> exp (-1).

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py).
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


/-! Combinatorial meaning: involutions of Fin n with no adjacent transposition. -/

/-! Involutions as functions. -/

theorem ite_neg' {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem ite_pos' {α : Sort*} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

/-- f is an involution. -/
def IsInvol {m : ℕ} (f : Fin m → Fin m) : Prop := ∀ i, f (f i) = i

/-- Extend g by fixing the last point. -/
def ext {m : ℕ} (g : Fin m → Fin m) : Fin (m + 1) → Fin (m + 1) :=
  fun i => Fin.lastCases (Fin.last m) (fun k => (g k).castSucc) i

/-- Extend g (which fixes j) by swapping j with the last point. -/
def ext2 {m : ℕ} (j : Fin m) (g : Fin m → Fin m) : Fin (m + 1) → Fin (m + 1) :=
  fun i => Fin.lastCases j.castSucc (fun k => if k = j then Fin.last m else (g k).castSucc) i

/-- Restrict f to the first m points; a point sent to the last point becomes fixed. -/
def res {m : ℕ} (f : Fin (m + 1) → Fin (m + 1)) : Fin m → Fin m :=
  fun k => if h : f k.castSucc = Fin.last m then k else (f k.castSucc).castPred h

@[simp] theorem ext_last {m : ℕ} (g : Fin m → Fin m) : ext g (Fin.last m) = Fin.last m := by
  simp [ext]

@[simp] theorem ext_castSucc {m : ℕ} (g : Fin m → Fin m) (k : Fin m) :
    ext g k.castSucc = (g k).castSucc := by
  simp [ext]

@[simp] theorem ext2_last {m : ℕ} (j : Fin m) (g : Fin m → Fin m) :
    ext2 j g (Fin.last m) = j.castSucc := by
  simp [ext2]

theorem ext2_castSucc {m : ℕ} (j : Fin m) (g : Fin m → Fin m) (k : Fin m) :
    ext2 j g k.castSucc = if k = j then Fin.last m else (g k).castSucc := by
  simp [ext2]

theorem invol_ne_last {m : ℕ} {f : Fin (m + 1) → Fin (m + 1)} (hf : IsInvol f)
    (hl : f (Fin.last m) = Fin.last m) (k : Fin m) : f k.castSucc ≠ Fin.last m := by
  intro h
  have := hf k.castSucc
  rw [h, hl] at this
  exact (Fin.castSucc_lt_last k).ne this.symm

theorem res_of_ne {m : ℕ} {f : Fin (m + 1) → Fin (m + 1)} {k : Fin m}
    (h : f k.castSucc ≠ Fin.last m) : (res f k).castSucc = f k.castSucc := by
  simp [res, h]

theorem res_of_eq {m : ℕ} {f : Fin (m + 1) → Fin (m + 1)} {k : Fin m}
    (h : f k.castSucc = Fin.last m) : res f k = k := by
  simp [res, h]

theorem ext_res {m : ℕ} {f : Fin (m + 1) → Fin (m + 1)} (hf : IsInvol f)
    (hl : f (Fin.last m) = Fin.last m) : ext (res f) = f := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [hl]
  · rw [ext_castSucc, res_of_ne (invol_ne_last hf hl k)]

theorem res_ext {m : ℕ} (g : Fin m → Fin m) : res (ext g) = g := by
  funext k
  have h : ext g k.castSucc ≠ Fin.last m := by
    rw [ext_castSucc]; exact (Fin.castSucc_lt_last _).ne
  apply Fin.castSucc_injective
  rw [res_of_ne h, ext_castSucc]

theorem ext_invol {m : ℕ} {g : Fin m → Fin m} (hg : IsInvol g) : IsInvol (ext g) := by
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp
  · simp [hg k]

theorem res_invol {m : ℕ} {f : Fin (m + 1) → Fin (m + 1)} (hf : IsInvol f)
    (hl : f (Fin.last m) = Fin.last m) : IsInvol (res f) := by
  have h := ext_res hf hl
  intro k
  apply Fin.castSucc_injective
  have e1 : ext (res f) (ext (res f) k.castSucc) = k.castSucc := by rw [h]; exact hf _
  simpa using e1

/-- The fibre f (last) = last. -/
def E1 {m : ℕ} (Q : (Fin (m + 1) → Fin (m + 1)) → Prop) :
    {f : Fin (m + 1) → Fin (m + 1) // IsInvol f ∧ f (Fin.last m) = Fin.last m ∧ Q f} ≃
      {g : Fin m → Fin m // IsInvol g ∧ Q (ext g)} where
  toFun f := ⟨res f.1, res_invol f.2.1 f.2.2.1, by rw [ext_res f.2.1 f.2.2.1]; exact f.2.2.2⟩
  invFun g := ⟨ext g.1, ext_invol g.2.1, ext_last _, g.2.2⟩
  left_inv f := Subtype.ext (ext_res f.2.1 f.2.2.1)
  right_inv g := Subtype.ext (res_ext g.1)

theorem ext2_res {m : ℕ} {f : Fin (m + 1) → Fin (m + 1)} (hf : IsInvol f) {j : Fin m}
    (hl : f (Fin.last m) = j.castSucc) : ext2 j (res f) = f := by
  have hj : f j.castSucc = Fin.last m := by rw [← hl]; exact hf _
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [hl]
  · rw [ext2_castSucc]
    by_cases hk : k = j
    · subst hk; simp [hj]
    · rw [ite_neg' hk]
      have hne : f k.castSucc ≠ Fin.last m := by
        intro h
        have := hf k.castSucc
        rw [h, hl] at this
        exact hk (Fin.castSucc_injective _ this.symm)
      rw [res_of_ne hne]

theorem res_ext2 {m : ℕ} {j : Fin m} {g : Fin m → Fin m} (hj : g j = j) : res (ext2 j g) = g := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [res_of_eq (by rw [ext2_castSucc, ite_pos' rfl]), hj]
  · have h : ext2 j g k.castSucc ≠ Fin.last m := by
      rw [ext2_castSucc, ite_neg' hk]; exact (Fin.castSucc_lt_last _).ne
    apply Fin.castSucc_injective
    rw [res_of_ne h, ext2_castSucc, ite_neg' hk]

theorem ext2_invol {m : ℕ} {j : Fin m} {g : Fin m → Fin m} (hg : IsInvol g) (hj : g j = j) :
    IsInvol (ext2 j g) := by
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [ext2_castSucc]
  · rw [ext2_castSucc]
    by_cases hk : k = j
    · subst hk; simp
    · rw [ite_neg' hk, ext2_castSucc]
      have : g k ≠ j := by
        intro h; apply hk; rw [← hg k, h, hj]
      rw [ite_neg' this, hg k]

theorem res_invol2 {m : ℕ} {f : Fin (m + 1) → Fin (m + 1)} (hf : IsInvol f) {j : Fin m}
    (hl : f (Fin.last m) = j.castSucc) : IsInvol (res f) ∧ res f j = j := by
  have h := ext2_res hf hl
  have hj : f j.castSucc = Fin.last m := by rw [← hl]; exact hf _
  have hrj : res f j = j := res_of_eq hj
  refine ⟨fun k => ?_, hrj⟩
  by_cases hk : k = j
  · subst hk; rw [hrj, hrj]
  · have hne : f k.castSucc ≠ Fin.last m := by
      intro h'
      have := hf k.castSucc
      rw [h', hl] at this
      exact hk (Fin.castSucc_injective _ this.symm)
    have hne2 : f (res f k).castSucc ≠ Fin.last m := by
      rw [res_of_ne hne, hf]; exact (Fin.castSucc_lt_last _).ne
    apply Fin.castSucc_injective
    rw [res_of_ne hne2, res_of_ne hne, hf]

/-- The fibre f (last) = j. -/
def E2 {m : ℕ} (j : Fin m) (Q : (Fin (m + 1) → Fin (m + 1)) → Prop) :
    {f : Fin (m + 1) → Fin (m + 1) // IsInvol f ∧ f (Fin.last m) = j.castSucc ∧ Q f} ≃
      {g : Fin m → Fin m // IsInvol g ∧ g j = j ∧ Q (ext2 j g)} where
  toFun f := ⟨res f.1, (res_invol2 f.2.1 f.2.2.1).1, (res_invol2 f.2.1 f.2.2.1).2,
    by rw [ext2_res f.2.1 f.2.2.1]; exact f.2.2.2⟩
  invFun g := ⟨ext2 j g.1, ext2_invol g.2.1 g.2.2.1, ext2_last _ _, g.2.2.2⟩
  left_inv f := Subtype.ext (ext2_res f.2.1 f.2.2.1)
  right_inv g := Subtype.ext (res_ext2 g.2.2.1)

/-- Split by the image of the last point. -/
theorem invol_split {m : ℕ} (Q : (Fin (m + 1) → Fin (m + 1)) → Prop) :
    Nat.card {f : Fin (m + 1) → Fin (m + 1) // IsInvol f ∧ Q f} =
      Nat.card {g : Fin m → Fin m // IsInvol g ∧ Q (ext g)} +
        ∑ j : Fin m, Nat.card {g : Fin m → Fin m // IsInvol g ∧ g j = j ∧ Q (ext2 j g)} := by
  have e : {f : Fin (m + 1) → Fin (m + 1) // IsInvol f ∧ Q f} ≃
      Σ v : Fin (m + 1), {f : Fin (m + 1) → Fin (m + 1) // IsInvol f ∧ f (Fin.last m) = v ∧ Q f} :=
    { toFun := fun f => ⟨f.1 (Fin.last m), f.1, f.2.1, rfl, f.2.2⟩
      invFun := fun x => ⟨x.2.1, x.2.2.1, x.2.2.2.2⟩
      left_inv := fun f => rfl
      right_inv := fun x => by
        obtain ⟨v, f, h1, h2, h3⟩ := x
        subst h2
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma, Fin.sum_univ_castSucc, add_comm]
  congr 1
  · exact Nat.card_congr (E1 Q)
  · exact Finset.sum_congr rfl (fun j _ => Nat.card_congr (E2 j Q))

theorem card_zero_of {α : Type*} {P : α → Prop} (h : ∀ x, ¬ P x) : Nat.card {x // P x} = 0 := by
  have : IsEmpty {x // P x} := ⟨fun x => h x.1 x.2⟩
  exact Nat.card_of_isEmpty

theorem card_congr_prop {α : Type*} {P R : α → Prop} (h : ∀ x, P x ↔ R x) :
    Nat.card {x // P x} = Nat.card {x // R x} :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

theorem inv_step (t : ℕ) : inv t + t * inv (t - 1) = inv (t + 1) := by
  rcases t with _ | t
  · rfl
  · rw [inv_succ_succ]; simp

/-- Points of D below the last one, as a subset of Fin m. -/
def Dres {m : ℕ} (D : Finset (Fin (m + 1))) : Finset (Fin m) :=
  univ.filter (fun k : Fin m => k.castSucc ∈ D)

theorem Dres_card {m : ℕ} (D : Finset (Fin (m + 1))) :
    (Dres D).card + (if Fin.last m ∈ D then 1 else 0) = D.card := by
  have h1 : D.card = ∑ i : Fin (m + 1), if i ∈ D then 1 else 0 := by
    rw [Finset.sum_boole]; simp
  have h2 : (Dres D).card = ∑ k : Fin m, if k.castSucc ∈ D then 1 else 0 := by
    rw [Finset.sum_boole]; simp [Dres]
  rw [h1, h2, Fin.sum_univ_castSucc]

theorem mem_Dres {m : ℕ} {D : Finset (Fin (m + 1))} {k : Fin m} : k ∈ Dres D ↔ k.castSucc ∈ D := by
  simp [Dres]

/-- Hypotheses for the restricted prescription (Dres D, res p). -/
theorem hyp_res {m : ℕ} {D : Finset (Fin (m + 1))} {p : Fin (m + 1) → Fin (m + 1)}
    (hp : ∀ i ∈ D, p i ∈ D ∧ p (p i) = i) :
    ∀ k ∈ Dres D, res p k ∈ Dres D ∧ res p (res p k) = k := by
  intro k hk
  rw [mem_Dres] at hk
  by_cases h : p k.castSucc = Fin.last m
  · rw [res_of_eq h]
    exact ⟨mem_Dres.mpr hk, res_of_eq h⟩
  · have e1 := res_of_ne h
    have hm : (res p k).castSucc ∈ D := by rw [e1]; exact (hp _ hk).1
    have h2 : p (res p k).castSucc ≠ Fin.last m := by
      rw [e1, (hp _ hk).2]; exact (Fin.castSucc_lt_last _).ne
    refine ⟨mem_Dres.mpr hm, Fin.castSucc_injective _ ?_⟩
    rw [res_of_ne h2, e1, (hp _ hk).2]

/-- Number of involutions with prescribed values p on D (p an involution of D). -/
theorem count_gen : ∀ (m : ℕ) (D : Finset (Fin m)) (p : Fin m → Fin m),
    (∀ i ∈ D, p i ∈ D ∧ p (p i) = i) →
    Nat.card {f : Fin m → Fin m // IsInvol f ∧ ∀ i ∈ D, f i = p i} = inv (m - D.card) := by
  intro m
  induction m with
  | zero =>
    intro D p _
    have : Unique {f : Fin 0 → Fin 0 // IsInvol f ∧ ∀ i ∈ D, f i = p i} :=
      { default := ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
        uniq := fun f => Subtype.ext (funext fun i => i.elim0) }
    rw [Nat.card_unique]
    simp
    rfl
  | succ m ih =>
    intro D p hp
    rw [invol_split]
    have hc := Dres_card D
    have hIH := ih (Dres D) (res p) (hyp_res hp)
    -- Q (ext g) ↔ prescription on Dres D, when last ∈ D forces p last = last.
    have hext : (Fin.last m ∈ D → p (Fin.last m) = Fin.last m) →
        ∀ g : Fin m → Fin m, (IsInvol g ∧ ∀ i ∈ D, ext g i = p i) ↔
          (IsInvol g ∧ ∀ k ∈ Dres D, g k = res p k) := by
      intro hl g
      have hne : ∀ k ∈ Dres D, p k.castSucc ≠ Fin.last m := by
        intro k hk h
        rw [mem_Dres] at hk
        by_cases hL : Fin.last m ∈ D
        · have := (hp _ hk).2
          rw [h, hl hL] at this
          exact (Fin.castSucc_lt_last k).ne this.symm
        · exact hL (h ▸ (hp _ hk).1)
      refine and_congr_right (fun _ => ⟨fun h k hk => ?_, fun h i hi => ?_⟩)
      · apply Fin.castSucc_injective
        rw [res_of_ne (hne k hk), ← h _ (mem_Dres.mp hk), ext_castSucc]
      · refine Fin.lastCases ?_ (fun k hi => ?_) i hi
        · intro hL; rw [ext_last, hl hL]
        · rw [ext_castSucc, h k (mem_Dres.mpr hi), res_of_ne (hne k (mem_Dres.mpr hi))]
    by_cases hL : Fin.last m ∈ D
    · obtain ⟨hpD, -⟩ := hp _ hL
      have hc' : (Dres D).card + 1 = D.card := by simpa [hL] using hc
      revert hpD
      refine Fin.lastCases (motive := fun v => p (Fin.last m) = v → v ∈ D → _) ?_ (fun j0 => ?_)
        (p (Fin.last m)) rfl
      · -- p last = last
        intro hpl _
        rw [card_congr_prop (hext (fun _ => hpl)), hIH]
        rw [Finset.sum_eq_zero (fun j _ => card_zero_of (fun g h => by
          have := h.2.2 _ hL
          rw [ext2_last, hpl] at this
          exact (Fin.castSucc_lt_last j).ne this))]
        have : m - (Dres D).card = m + 1 - D.card := by omega
        rw [this, add_zero]
      · -- p last = j0
        intro hpl hj0D
        have hz : Nat.card {g : Fin m → Fin m // IsInvol g ∧ ∀ i ∈ D, ext g i = p i} = 0 :=
          card_zero_of (fun g h => by
            have := h.2 _ hL
            rw [ext_last, hpl] at this
            exact (Fin.castSucc_lt_last j0).ne this.symm)
        rw [hz, zero_add, Finset.sum_eq_single j0]
        · have hpj0 : p j0.castSucc = Fin.last m := by rw [← hpl]; exact (hp _ hL).2
          have hres0 : res p j0 = j0 := res_of_eq hpj0
          rw [card_congr_prop (R := fun g => IsInvol g ∧ ∀ k ∈ Dres D, g k = res p k), hIH]
          · congr 1; omega
          intro g
          refine and_congr_right (fun _ => ⟨fun h k hk => ?_, fun h => ⟨?_, fun i hi => ?_⟩⟩)
          · by_cases hk0 : k = j0
            · subst hk0; rw [hres0]; exact h.1
            · have hne : p k.castSucc ≠ Fin.last m := by
                intro h'
                have := (hp _ (mem_Dres.mp hk)).2
                rw [h', hpl] at this
                exact hk0 (Fin.castSucc_injective _ this.symm)
              apply Fin.castSucc_injective
              have := h.2 _ (mem_Dres.mp hk)
              rw [ext2_castSucc, ite_neg' hk0] at this
              rw [this, res_of_ne hne]
          · rw [h j0 (mem_Dres.mpr hj0D), hres0]
          · refine Fin.lastCases ?_ (fun k hi => ?_) i hi
            · intro _; rw [ext2_last, hpl]
            · rw [ext2_castSucc]
              by_cases hk0 : k = j0
              · subst hk0; rw [ite_pos' rfl, hpj0]
              · rw [ite_neg' hk0, h k (mem_Dres.mpr hi)]
                have hne : p k.castSucc ≠ Fin.last m := by
                  intro h'
                  have := (hp _ hi).2
                  rw [h', hpl] at this
                  exact hk0 (Fin.castSucc_injective _ this.symm)
                rw [res_of_ne hne]
        · intro j _ hj
          exact card_zero_of (fun g h => by
            have := h.2.2 _ hL
            rw [ext2_last, hpl] at this
            exact hj (Fin.castSucc_injective _ this))
        · intro h; exact absurd (Finset.mem_univ j0) h
    · -- last ∉ D
      have hc' : (Dres D).card = D.card := by simpa [hL] using hc
      rw [card_congr_prop (hext (fun h => absurd h hL)), hIH]
      have hterm : ∀ j : Fin m,
          Nat.card {g : Fin m → Fin m // IsInvol g ∧ g j = j ∧ ∀ i ∈ D, ext2 j g i = p i} =
            if j.castSucc ∈ D then 0 else inv (m - (D.card + 1)) := by
        intro j
        by_cases hjD : j.castSucc ∈ D
        · rw [ite_pos' hjD]
          exact card_zero_of (fun g h => by
            have := h.2.2 _ hjD
            rw [ext2_castSucc, ite_pos' rfl] at this
            exact hL (this ▸ (hp _ hjD).1))
        · rw [ite_neg' hjD]
          have hjn : j ∉ Dres D := fun h => hjD (mem_Dres.mp h)
          have hyp2 : ∀ k ∈ insert j (Dres D), Function.update (res p) j j k ∈ insert j (Dres D) ∧
              Function.update (res p) j j (Function.update (res p) j j k) = k := by
            intro k hk
            rcases Finset.mem_insert.mp hk with rfl | hk
            · simp
            · have hkj : k ≠ j := fun h => hjn (h ▸ hk)
              have h1 := hyp_res hp k hk
              have hkj2 : res p k ≠ j := fun h => hjn (h ▸ h1.1)
              rw [Function.update_of_ne hkj, Function.update_of_ne hkj2]
              exact ⟨Finset.mem_insert_of_mem h1.1, h1.2⟩
          have hIH2 := ih (insert j (Dres D)) (Function.update (res p) j j) hyp2
          rw [Finset.card_insert_of_notMem hjn, hc'] at hIH2
          rw [← hIH2]
          apply card_congr_prop
          intro g
          have hne : ∀ k ∈ Dres D, p k.castSucc ≠ Fin.last m := fun k hk h =>
            hL (h ▸ (hp _ (mem_Dres.mp hk)).1)
          refine and_congr_right (fun _ => ⟨fun h k hk => ?_, fun h => ⟨?_, fun i hi => ?_⟩⟩)
          · rcases Finset.mem_insert.mp hk with rfl | hk
            · simp [h.1]
            · have hkj : k ≠ j := fun h => hjn (h ▸ hk)
              rw [Function.update_of_ne hkj]
              apply Fin.castSucc_injective
              have := h.2 _ (mem_Dres.mp hk)
              rw [ext2_castSucc, ite_neg' hkj] at this
              rw [this, res_of_ne (hne k hk)]
          · have := h j (Finset.mem_insert_self _ _)
            simpa using this
          · refine Fin.lastCases ?_ (fun k hi => ?_) i hi
            · intro h'; exact absurd h' hL
            · have hk : k ∈ Dres D := mem_Dres.mpr hi
              have hkj : k ≠ j := fun h => hjn (h ▸ hk)
              rw [ext2_castSucc, ite_neg' hkj, h k (Finset.mem_insert_of_mem hk),
                Function.update_of_ne hkj, res_of_ne (hne k hk)]
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite, Finset.sum_const_zero,
        zero_add, Finset.sum_const, smul_eq_mul]
      have hcnt : (univ.filter (fun j : Fin m => ¬ j.castSucc ∈ D)).card = m - D.card := by
        have := Finset.card_filter_add_card_filter_not
          (s := (univ : Finset (Fin m))) (fun j : Fin m => j.castSucc ∈ D)
        have h3 : (univ.filter (fun j : Fin m => j.castSucc ∈ D)).card = D.card := by
          rw [← hc']; rfl
        simp only [card_univ, Fintype.card_fin] at this
        omega
      rw [hcnt]
      have hle : D.card ≤ m := by
        rw [← hc']; exact (Finset.card_le_univ _).trans (by simp)
      have e1 : m - (D.card + 1) = (m - D.card) - 1 := by omega
      have e2 : m + 1 - D.card = (m - D.card) + 1 := by omega
      rw [hc', e1, e2, inv_step]

/-! Sets of pairwise non-adjacent positions. -/

/-- K ⊆ {0, ..., n-2} (as the left ends of adjacent pairs {i, i+1} in [0, n)), no two consecutive. -/
abbrev Good (n : ℕ) (K : Finset ℕ) : Prop := ∀ i ∈ K, i + 1 < n ∧ i + 1 ∉ K

/-- Weighted count of good sets. -/
def Sg (n : ℕ) (w : ℕ → ℤ) : ℤ := ∑ K ∈ (range n).powerset, if Good n K then w K.card else 0

/-- Binomial form. -/
def Bg (n : ℕ) (w : ℕ → ℤ) : ℤ := ∑ k ∈ range (n + 1), ((n - k).choose k : ℤ) * w k

theorem Sg_drop (m : ℕ) (w : ℕ → ℤ) :
    Sg (m + 1) w = ∑ K ∈ (range m).powerset, if Good (m + 1) K then w K.card else 0 := by
  unfold Sg
  rw [range_add_one, powerset_insert, sum_union]
  · rw [sum_image]
    · have : ∑ K ∈ (range m).powerset,
          (if Good (m + 1) (insert m K) then w (insert m K).card else 0) = 0 := by
        apply sum_eq_zero
        intro K _
        rw [ite_neg']
        intro h
        have := (h m (mem_insert_self _ _)).1
        omega
      rw [this, add_zero]
    · intro K1 h1 K2 h2 he
      have h1' : m ∉ K1 := fun h => by simpa using (mem_powerset.mp h1) h
      have h2' : m ∉ K2 := fun h => by simpa using (mem_powerset.mp h2) h
      rw [← erase_insert h1', ← erase_insert h2', he]
  · rw [disjoint_left]
    intro K hK hK'
    obtain ⟨K', -, rfl⟩ := mem_image.mp hK'
    have := (mem_powerset.mp hK) (mem_insert_self m K')
    simp at this

theorem Sg_rec (n : ℕ) (w : ℕ → ℤ) : Sg (n + 2) w = Sg (n + 1) w + Sg n (fun k => w (k + 1)) := by
  rw [Sg_drop (n + 1), Sg_drop n]
  rw [range_add_one, powerset_insert, sum_union]
  · rw [sum_image]
    · congr 1
      · apply sum_congr rfl
        intro K hK
        have hK' := mem_powerset.mp hK
        have : Good (n + 2) K ↔ Good (n + 1) K := by
          constructor
          · intro h i hi; have := hK' hi; simp at this; exact ⟨by omega, (h i hi).2⟩
          · intro h i hi; exact ⟨by have := (h i hi).1; omega, (h i hi).2⟩
        simp only [this]
      · unfold Sg
        apply sum_congr rfl
        intro K hK
        have hK' := mem_powerset.mp hK
        have hn : n ∉ K := fun h => by simpa using hK' h
        have : Good (n + 2) (insert n K) ↔ Good n K := by
          constructor
          · intro h i hi
            have h1 := h i (mem_insert_of_mem hi)
            have h2 : i + 1 ≠ n := fun e => h1.2 (e ▸ mem_insert_self _ _)
            have h3 := hK' hi
            simp at h3
            exact ⟨by omega, fun h4 => h1.2 (mem_insert_of_mem h4)⟩
          · intro h i hi
            rcases mem_insert.mp hi with rfl | hi
            · refine ⟨by omega, ?_⟩
              intro h4
              rcases mem_insert.mp h4 with h5 | h5
              · omega
              · have := hK' h5; simp at this
            · refine ⟨by have := (h i hi).1; omega, ?_⟩
              intro h4
              rcases mem_insert.mp h4 with h5 | h5
              · have := (h i hi).1; omega
              · exact (h i hi).2 h5
        simp only [this, card_insert_of_notMem hn]
    · intro K1 h1 K2 h2 he
      have h1' : n ∉ K1 := fun h => by simpa using (mem_powerset.mp h1) h
      have h2' : n ∉ K2 := fun h => by simpa using (mem_powerset.mp h2) h
      rw [← erase_insert h1', ← erase_insert h2', he]
  · rw [disjoint_left]
    intro K hK hK'
    obtain ⟨K', -, rfl⟩ := mem_image.mp hK'
    have := (mem_powerset.mp hK) (mem_insert_self n K')
    simp at this

theorem Bg_rec (n : ℕ) (w : ℕ → ℤ) : Bg (n + 2) w = Bg (n + 1) w + Bg n (fun k => w (k + 1)) := by
  unfold Bg
  have L : ∑ k ∈ range (n + 2 + 1), ((n + 2 - k).choose k : ℤ) * w k =
      ∑ j ∈ range (n + 2), ((n + 2 - (j + 1)).choose (j + 1) : ℤ) * w (j + 1) + w 0 := by
    rw [sum_range_succ']; simp
  have R1 : ∑ k ∈ range (n + 1 + 1), ((n + 1 - k).choose k : ℤ) * w k =
      ∑ j ∈ range (n + 1), ((n + 1 - (j + 1)).choose (j + 1) : ℤ) * w (j + 1) + w 0 := by
    rw [sum_range_succ']; simp
  have hterm : ∀ j ∈ range (n + 2), ((n + 2 - (j + 1)).choose (j + 1) : ℤ) * w (j + 1) =
      ((n + 1 - (j + 1)).choose (j + 1) : ℤ) * w (j + 1) + ((n - j).choose j : ℤ) * w (j + 1) := by
    intro j _
    have e1 : n + 2 - (j + 1) = n + 1 - j := by omega
    have e2 : n + 1 - (j + 1) = n - j := by omega
    rw [e1, e2]
    rcases Nat.lt_or_ge n j with h | h
    · have e3 : n + 1 - j = 0 := by omega
      have e4 : n - j = 0 := by omega
      rw [e3, e4]
      rw [Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1), Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
      simp
    · have e3 : n + 1 - j = (n - j) + 1 := by omega
      rw [e3, Nat.choose_succ_succ']
      push_cast
      ring
  rw [L, R1, sum_congr rfl hterm, sum_add_distrib, sum_range_succ _ (n + 1),
    sum_range_succ (fun j => ((n - j).choose j : ℤ) * w (j + 1)) (n + 1)]
  have z1 : ((n + 1 - (n + 1 + 1)).choose (n + 1 + 1) : ℤ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have z2 : ((n - (n + 1)).choose (n + 1) : ℤ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [z1, z2]
  ring

theorem Sg_eq_Bg : ∀ n (w : ℕ → ℤ), Sg n w = Bg n w
  | 0, w => by simp [Sg, Bg]
  | 1, w => by
    unfold Sg Bg
    rw [show (range 1).powerset = {∅, {0}} by decide]
    have h2 : ¬ Good 1 {0} := fun h => by have := (h 0 (by simp)).1; omega
    simp [sum_range_succ, h2]
  | (n + 2), w => by
    rw [Sg_rec, Bg_rec, Sg_eq_Bg (n + 1), Sg_eq_Bg n]

/-! Involutions containing a prescribed set of adjacent transpositions. -/

/-- f contains the adjacent transposition (i i+1) for every i ∈ K. -/
def Adj {n : ℕ} (K : Finset ℕ) (f : Fin n → Fin n) : Prop :=
  ∀ i ∈ K, ∃ a : Fin n, a.val = i ∧ (f a).val = i + 1

theorem adj_zero_of_not_good {n : ℕ} {K : Finset ℕ} (hg : ¬ Good n K) :
    Nat.card {f : Fin n → Fin n // IsInvol f ∧ Adj K f} = 0 := by
  apply card_zero_of
  intro f ⟨hf, hA⟩
  apply hg
  intro i hi
  obtain ⟨a, ha, hfa⟩ := hA i hi
  refine ⟨by have := (f a).isLt; omega, fun hi1 => ?_⟩
  obtain ⟨b, hb, hfb⟩ := hA (i + 1) hi1
  have e : f a = b := Fin.ext (by rw [hfa, hb])
  have := hf a
  rw [e] at this
  rw [this] at hfb
  omega

/-- Positions covered by the pairs {i, i+1}, i ∈ K. -/
def Dk (n : ℕ) (K : Finset ℕ) : Finset (Fin n) :=
  univ.filter (fun a : Fin n => a.val ∈ K ∨ (1 ≤ a.val ∧ a.val - 1 ∈ K))

theorem dite_pos' {α : Sort*} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬c → α} :
    dite c a b = a h := by simp [h]

theorem dite_neg' {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) {a : c → α} {b : ¬c → α} :
    dite c a b = b h := by simp [h]

/-- The prescribed partner. -/
def pk {n : ℕ} (K : Finset ℕ) (a : Fin n) : Fin n :=
  if h : a.val ∈ K ∧ a.val + 1 < n then ⟨a.val + 1, h.2⟩
  else if h' : 1 ≤ a.val ∧ a.val - 1 ∈ K then ⟨a.val - 1, by omega⟩ else a

theorem pk_up {n : ℕ} {K : Finset ℕ} (hg : Good n K) {a : Fin n} (h : a.val ∈ K) :
    (pk K a).val = a.val + 1 := by
  unfold pk
  rw [dite_pos' ⟨h, (hg _ h).1⟩]

theorem pk_down {n : ℕ} {K : Finset ℕ} (hg : Good n K) {a : Fin n} (h1 : 1 ≤ a.val)
    (h2 : a.val - 1 ∈ K) : (pk K a).val = a.val - 1 := by
  have hnot : a.val ∉ K := by
    have := (hg _ h2).2
    rwa [show a.val - 1 + 1 = a.val by omega] at this
  unfold pk
  rw [dite_neg' (fun h => hnot h.1), dite_pos' ⟨h1, h2⟩]

theorem hyp_pk {n : ℕ} {K : Finset ℕ} (hg : Good n K) :
    ∀ a ∈ Dk n K, pk K a ∈ Dk n K ∧ pk K (pk K a) = a := by
  intro a ha
  simp only [Dk, mem_filter, mem_univ, true_and] at ha ⊢
  rcases ha with h | ⟨h1, h2⟩
  · have e := pk_up hg h
    refine ⟨Or.inr ⟨by omega, by rw [e]; simpa using h⟩, Fin.ext ?_⟩
    rw [pk_down hg (by omega) (by rw [e]; simpa using h), e]
    omega
  · have e := pk_down hg h1 h2
    refine ⟨Or.inl (by rw [e]; exact h2), Fin.ext ?_⟩
    rw [pk_up hg (by rw [e]; exact h2), e]
    omega

theorem adj_iff {n : ℕ} {K : Finset ℕ} (hg : Good n K) {f : Fin n → Fin n} (hf : IsInvol f) :
    Adj K f ↔ ∀ a ∈ Dk n K, f a = pk K a := by
  constructor
  · intro hA a ha
    simp only [Dk, mem_filter, mem_univ, true_and] at ha
    rcases ha with h | ⟨h1, h2⟩
    · obtain ⟨b, hb, hfb⟩ := hA _ h
      have e : b = a := Fin.ext hb
      subst e
      exact Fin.ext (by rw [hfb, pk_up hg h])
    · obtain ⟨b, hb, hfb⟩ := hA _ h2
      have e : f b = a := Fin.ext (by rw [hfb]; omega)
      have e2 : f a = b := by rw [← e]; exact hf b
      exact Fin.ext (by rw [e2, pk_down hg h1 h2, hb])
  · intro h i hi
    have hlt := (hg i hi).1
    refine ⟨⟨i, by omega⟩, rfl, ?_⟩
    have hm : (⟨i, by omega⟩ : Fin n) ∈ Dk n K := by simp [Dk, hi]
    rw [h _ hm, pk_up hg hi]

theorem card_Dk {n : ℕ} {K : Finset ℕ} (hg : Good n K) : (Dk n K).card = 2 * K.card := by
  have hsplit : Dk n K = univ.filter (fun a : Fin n => a.val ∈ K) ∪
      univ.filter (fun a : Fin n => 1 ≤ a.val ∧ a.val - 1 ∈ K) := by
    unfold Dk; rw [filter_or]
  have hdisj : Disjoint (univ.filter (fun a : Fin n => a.val ∈ K))
      (univ.filter (fun a : Fin n => 1 ≤ a.val ∧ a.val - 1 ∈ K)) := by
    rw [disjoint_filter]
    intro a _ h ⟨h1, h2⟩
    have := (hg _ h2).2
    rw [show a.val - 1 + 1 = a.val by omega] at this
    exact this h
  have c1 : (univ.filter (fun a : Fin n => a.val ∈ K)).card = K.card := by
    apply card_bij (fun a _ => a.val)
    · intro a ha; simpa using ha
    · intro a _ b _ h; exact Fin.ext h
    · intro k hk
      exact ⟨⟨k, by have := (hg k hk).1; omega⟩, by simpa using hk, rfl⟩
  have c2 : (univ.filter (fun a : Fin n => 1 ≤ a.val ∧ a.val - 1 ∈ K)).card = K.card := by
    apply card_bij (fun a _ => a.val - 1)
    · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha; exact ha.2
    · intro a ha b hb h
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact Fin.ext (by omega)
    · intro k hk
      refine ⟨⟨k + 1, (hg k hk).1⟩, by simpa using hk, rfl⟩
  rw [hsplit, card_union_of_disjoint hdisj, c1, c2]
  ring

theorem count_adj (n : ℕ) (K : Finset ℕ) :
    Nat.card {f : Fin n → Fin n // IsInvol f ∧ Adj K f} =
      if Good n K then inv (n - 2 * K.card) else 0 := by
  by_cases hg : Good n K
  · rw [ite_pos' hg, ← card_Dk hg, ← count_gen n (Dk n K) (pk K) (hyp_pk hg)]
    exact card_congr_prop (fun f => and_congr_right (fun hf => adj_iff hg hf))
  · rw [ite_neg' hg]
    exact adj_zero_of_not_good hg

/-! Inclusion–exclusion. -/

open Classical in
theorem natcard_eq_filter {α : Type*} [Fintype α] (P : α → Prop) :
    Nat.card {x // P x} = (univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
theorem ie_point {n : ℕ} (f : Fin n → Fin n) :
    (∑ K ∈ (range n).powerset, if Adj K f then (-1 : ℤ) ^ K.card else 0) =
      if ∀ i : Fin n, (f i).val ≠ i.val + 1 then 1 else 0 := by
  set T : Finset ℕ := (univ.filter (fun a : Fin n => (f a).val = a.val + 1)).image Fin.val with hT
  have hTr : T ⊆ range n := by
    intro x hx
    simp only [hT, mem_image, mem_filter, mem_univ, true_and] at hx
    obtain ⟨a, -, rfl⟩ := hx
    simp
  have hadj : ∀ K, Adj K f ↔ K ⊆ T := by
    intro K
    simp only [Adj, subset_iff, hT, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · intro h i hi
      obtain ⟨a, ha, hfa⟩ := h i hi
      exact ⟨a, by rw [hfa, ha], ha⟩
    · intro h i hi
      obtain ⟨a, hfa, ha⟩ := h hi
      exact ⟨a, ha, by rw [hfa, ha]⟩
  simp only [hadj]
  rw [← sum_filter]
  have hf : (range n).powerset.filter (fun K => K ⊆ T) = T.powerset := by
    ext K
    simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hTr, h⟩⟩
  rw [hf, sum_powerset_neg_one_pow_card]
  have hTe : T = ∅ ↔ ∀ i : Fin n, (f i).val ≠ i.val + 1 := by
    simp only [hT, image_eq_empty, filter_eq_empty_iff, mem_univ, true_implies]
  by_cases h : ∀ i : Fin n, (f i).val ≠ i.val + 1
  · rw [ite_pos' (hTe.mpr h), ite_pos' h]
  · rw [ite_neg' (fun h' => h (hTe.mp h')), ite_neg' h]

open Classical in
theorem ie_count (n : ℕ) :
    (Nat.card {f : Fin n → Fin n // IsInvol f ∧ ∀ i : Fin n, (f i).val ≠ i.val + 1} : ℤ) =
      ∑ K ∈ (range n).powerset,
        (-1 : ℤ) ^ K.card * (Nat.card {f : Fin n → Fin n // IsInvol f ∧ Adj K f} : ℤ) := by
  simp only [natcard_eq_filter, card_filter]
  push_cast
  have h1 : ∀ f : Fin n → Fin n,
      (if IsInvol f ∧ ∀ i : Fin n, (f i).val ≠ i.val + 1 then (1 : ℤ) else 0) =
        ∑ K ∈ (range n).powerset, if IsInvol f ∧ Adj K f then (-1 : ℤ) ^ K.card else 0 := by
    intro f
    by_cases hf : IsInvol f
    · simp only [hf, true_and]
      exact (ie_point f).symm
    · simp [hf]
  rw [sum_congr rfl (fun f _ => h1 f), sum_comm]
  apply sum_congr rfl
  intro K _
  rw [mul_sum]
  apply sum_congr rfl
  intro f _
  by_cases h : IsInvol f ∧ Adj K f
  · simp [h]
  · simp [h]

/-! The count of the entry's definition. -/

/-- A170941 by its combinatorial definition: involutions σ of Fin n with no adjacent
transposition, i.e. no i with σ i = i + 1. -/
def A170941count (n : ℕ) : ℕ :=
  (univ.filter (fun σ : Equiv.Perm (Fin n) => σ * σ = 1 ∧ ∀ i : Fin n, (σ i).val ≠ i.val + 1)).card

/-- Involutive permutations are involutive functions. -/
def permEquiv (n : ℕ) :
    {σ : Equiv.Perm (Fin n) // σ * σ = 1 ∧ ∀ i : Fin n, (σ i).val ≠ i.val + 1} ≃
      {f : Fin n → Fin n // IsInvol f ∧ ∀ i : Fin n, (f i).val ≠ i.val + 1} where
  toFun σ := ⟨σ.1, fun i => by
      have h := Equiv.ext_iff.mp σ.2.1 i
      simpa [Equiv.Perm.mul_apply] using h, σ.2.2⟩
  invFun f := ⟨⟨f.1, f.1, f.2.1, f.2.1⟩, Equiv.ext fun i => f.2.1 i, f.2.2⟩
  left_inv σ := Subtype.ext (Equiv.ext fun _ => rfl)
  right_inv f := Subtype.ext rfl

theorem A170941count_eq (n : ℕ) : (A170941count n : ℤ) = a n := by
  have h0 : A170941count n =
      Nat.card {f : Fin n → Fin n // IsInvol f ∧ ∀ i : Fin n, (f i).val ≠ i.val + 1} := by
    rw [← Nat.card_congr (permEquiv n), natcard_eq_filter]
    unfold A170941count
    convert rfl
  rw [h0, ie_count]
  simp only [count_adj]
  have h1 : (∑ K ∈ (range n).powerset, (-1 : ℤ) ^ K.card *
      ((if Good n K then inv (n - 2 * K.card) else 0 : ℕ) : ℤ)) =
      Sg n (fun k => (-1 : ℤ) ^ k * (inv (n - 2 * k) : ℤ)) := by
    unfold Sg
    apply sum_congr rfl
    intro K _
    by_cases hg : Good n K
    · rw [ite_pos' hg, ite_pos' hg]
    · rw [ite_neg' hg, ite_neg' hg]
      simp
  rw [h1, Sg_eq_Bg, a_eq_b]
  unfold Bg b t
  apply sum_congr rfl
  intro k _
  ring

/-- Callan's conjecture for the combinatorial count: the proportion of involutions of [n]
with no adjacent transposition tends to 1/e. -/
theorem A170941count_tendsto :
    Tendsto (fun n => (A170941count n : ℝ) / inv n) atTop (𝓝 (Real.exp (-1))) := by
  refine A170941_tendsto.congr (fun n => ?_)
  rw [← A170941count_eq]
  push_cast
  rfl
