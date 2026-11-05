/-
OEIS A217876, Mathlib proof.

I(n): involution numbers (A000085), I(0) = I(1) = 1, I(n+2) = I(n+1) + (n+1) I(n).
T(n,k) = sum_i (-1)^(i+k) C(i,k) C(n-i,i) I(n-2i) (`T` below): the number of
involutions of [n] with exactly k adjacent transpositions (i i+1), by
inclusion-exclusion: C(n-i,i) counts sets of i disjoint adjacent pairs and
I(n-2i) the involutions containing a given such set. `T_data` checks the
first 9 rows against the entry.

Main theorem `A217876_conjecture`: for every j, T(n,j)/I(n) -> e^(-1)/j!,
the Poisson(1) probability of j. For an N-valued variable this pointwise
convergence is convergence in distribution, the conjecture.
`binom_moment_tendsto`: b i n = C(n-i,i) I(n-2i)/I(n) -> 1/i! (the binomial
moments E C(X_n,i) tend to those of Poisson(1)).

Proof. y(n) = I(n+1)/I(n) satisfies sqrt(n+1) <= y(n) <= sqrt(n+1) + 1
(`Y_bounds`), so c(n) = (n+1) I(n)/I(n+2) = 1/(1 + y(n)/(n+1)) -> 1.
b(i+1, n+2) = (1/(i+1)) ((n+1-i)/(n+1)) c(n) b(i, n) gives b i n -> 1/i! and
0 <= b i n <= 1/i! by induction on i. T(n,j)/I(n) = sum_i (-1)^(i+j) C(i,j) b i n
and Tannery's theorem (`tendsto_tsum_of_dominated_convergence`, dominating
series C(i,j)/i! <= 2^i/i!) gives the limit
sum_i (-1)^(i+j) C(i,j)/i! = e^(-1)/j!.

Checked: everything above, with T given by the inclusion-exclusion formula.
Not checked in Lean: that this formula counts involutions by adjacent
transpositions (standard inclusion-exclusion; checked by brute force for
n <= 10 in certificate/check.py), and the textbook fact that pointwise
convergence of probability mass functions on N is convergence in distribution.
-/
import Mathlib

open Filter Topology Finset

namespace A217876

/-- Involution numbers A000085. -/
def I : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => I (n + 1) + (n + 1) * I n

/-- T(n,k) = number of involutions of [n] with k adjacent transpositions (inclusion-exclusion). -/
def T (n k : ℕ) : ℤ :=
  ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (i + k) * ((i.choose k * (n - i).choose i * I (n - 2 * i) : ℕ) : ℤ)

theorem T_data :
    (List.range 9).map (fun n => (List.range (n / 2 + 1)).map (T n)) =
      [[1], [1], [1, 1], [2, 2], [5, 4, 1], [13, 10, 3], [37, 29, 9, 1], [112, 88, 28, 4],
        [363, 288, 96, 16, 1]] := by
  decide

theorem I_succ_succ (n : ℕ) : I (n + 2) = I (n + 1) + (n + 1) * I n := rfl

theorem I_pos : ∀ n, 0 < I n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have := I_pos (n + 1)
    rw [I_succ_succ]
    omega

theorem I_posR (n : ℕ) : (0 : ℝ) < I n := by exact_mod_cast I_pos n

/-- y(n) = I(n+1)/I(n). -/
noncomputable def Y (n : ℕ) : ℝ := (I (n + 1) : ℝ) / I n

theorem Y_bounds (n : ℕ) :
    Real.sqrt ((n : ℝ) + 1) ≤ Y n ∧ Y n ≤ Real.sqrt ((n : ℝ) + 1) + 1 := by
  induction n with
  | zero => simp [Y, I]
  | succ n ih =>
    obtain ⟨hl, hu⟩ := ih
    have h0 := I_posR n
    have h1 := I_posR (n + 1)
    have hY : Y (n + 1) = 1 + ((n : ℝ) + 1) / Y n := by
      unfold Y
      rw [I_succ_succ]
      push_cast
      field_simp
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    set s := Real.sqrt ((n : ℝ) + 1) with hsdef
    have hs : s ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr (by linarith)
    have ht : Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) ^ 2 = (n : ℝ) + 2 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    set t := Real.sqrt (((n + 1 : ℕ) : ℝ) + 1)
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hst : s ≤ t := by nlinarith
    have hYpos : 0 < Y n := by linarith
    set z := ((n : ℝ) + 1) / Y n with hz
    have hzY : z * Y n = (n : ℝ) + 1 := by rw [hz]; field_simp
    have hz0 : 0 ≤ z := by positivity
    rw [hY]
    constructor
    · by_contra h
      have h := not_le.mp h
      have h2 : s ^ 2 + s + 1 < t * (s + 1) := by nlinarith
      have h3 := mul_self_lt_mul_self (by positivity) h2
      nlinarith
    · have : z ≤ s := by nlinarith
      linarith

/-- c(n) = (n+1) I(n)/I(n+2). -/
noncomputable def c (n : ℕ) : ℝ := ((n : ℝ) + 1) * I n / I (n + 2)

theorem c_bounds (n : ℕ) : 0 ≤ c n ∧ c n ≤ 1 := by
  have h0 := I_posR n
  have h1 := I_posR (n + 1)
  have h2 := I_posR (n + 2)
  refine ⟨by unfold c; positivity, ?_⟩
  unfold c
  rw [div_le_one h2, I_succ_succ]
  push_cast
  linarith

theorem c_tendsto : Tendsto c atTop (𝓝 1) := by
  have hq : Tendsto (fun n : ℕ => Y n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => Real.sqrt (4 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4)
      rw [mul_zero] at this
      have h2 := (Real.continuous_sqrt.tendsto 0).comp this
      rw [Real.sqrt_zero] at h2
      exact h2
    apply squeeze_zero (fun n => ?_) (fun n => ?_) hb
    · have := (Y_bounds n).1
      have : 0 ≤ Y n := le_trans (Real.sqrt_nonneg _) this
      positivity
    · obtain ⟨hl, hu⟩ := Y_bounds n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hs : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hs1 : 1 ≤ Real.sqrt ((n : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith)
      have hY0 : 0 ≤ Y n := by linarith
      have hp : (0 : ℝ) < n + 1 := by positivity
      calc Y n / ((n : ℝ) + 1) = Real.sqrt ((Y n / ((n : ℝ) + 1)) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (4 * (1 / ((n : ℝ) + 1))) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow, div_le_iff₀ (by positivity)]
          field_simp
          nlinarith
  have hc : ∀ n, c n = (1 + Y n / ((n : ℝ) + 1))⁻¹ := by
    intro n
    have h0 := I_posR n
    have h1 := I_posR (n + 1)
    unfold c Y
    rw [I_succ_succ]
    push_cast
    field_simp
    ring
  have := ((tendsto_const_nhds (x := (1 : ℝ))).add hq).inv₀ (by norm_num)
  simp only [add_zero, inv_one] at this
  exact this.congr (fun n => (hc n).symm)

/-- b i n = C(n-i,i) I(n-2i)/I(n), the binomial moment E C(X_n, i). -/
noncomputable def b (i n : ℕ) : ℝ := ((n - i).choose i : ℝ) * I (n - 2 * i) / I n

theorem b_zero (n : ℕ) : b 0 n = 1 := by
  have := I_posR n
  unfold b
  simp only [Nat.sub_zero, Nat.choose_zero_right, mul_zero, Nat.cast_one, one_mul]
  exact div_self this.ne'

theorem b_nonneg (i n : ℕ) : 0 ≤ b i n := by
  have := I_posR n
  unfold b
  positivity

theorem b_vanish (i n : ℕ) (h : n < 2 * i) : b i n = 0 := by
  unfold b
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem b_rec (i n : ℕ) :
    b (i + 1) (n + 2) = (1 / ((i : ℝ) + 1)) * (((n + 1 - i : ℕ) : ℝ) / ((n : ℝ) + 1)) * c n * b i n := by
  have hch : (((n + 1 - i).choose (i + 1) : ℕ) : ℝ) * ((i : ℝ) + 1) =
      ((n + 1 - i : ℕ) : ℝ) * (((n - i).choose i : ℕ) : ℝ) := by
    rcases le_or_gt i n with h | h
    · have := Nat.add_one_mul_choose_eq (n - i) i
      rw [show n + 1 - i = n - i + 1 by omega]
      exact_mod_cast this.symm
    · rw [show n + 1 - i = 0 by omega]
      simp
  have h0 := I_posR n
  have h2 := I_posR (n + 2)
  unfold b c
  rw [show n + 2 - (i + 1) = n + 1 - i by omega, show n + 2 - 2 * (i + 1) = n - 2 * i by omega]
  have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linear_combination (I (n - 2 * i) : ℝ) * hch

theorem b_le (i : ℕ) : ∀ n, b i n ≤ 1 / (i.factorial : ℝ) := by
  induction i with
  | zero => intro n; rw [b_zero]; simp
  | succ i ih =>
    intro n
    rcases n with _ | _ | n
    · rw [b_vanish _ _ (by omega)]; positivity
    · rw [b_vanish _ _ (by omega)]; positivity
    rw [b_rec]
    obtain ⟨hc0, hc1⟩ := c_bounds n
    have hq0 : 0 ≤ ((n + 1 - i : ℕ) : ℝ) / ((n : ℝ) + 1) := by positivity
    have hq1 : ((n + 1 - i : ℕ) : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : ((n + 1 - i : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      push_cast at this
      linarith
    have hb0 := b_nonneg i n
    have hb1 := ih n
    have hprod : (((n + 1 - i : ℕ) : ℝ) / ((n : ℝ) + 1)) * c n * b i n ≤ 1 / (i.factorial : ℝ) := by
      calc (((n + 1 - i : ℕ) : ℝ) / ((n : ℝ) + 1)) * c n * b i n ≤ 1 * 1 * b i n := by
            apply mul_le_mul_of_nonneg_right _ hb0
            exact mul_le_mul hq1 hc1 hc0 zero_le_one
        _ ≤ 1 / (i.factorial : ℝ) := by linarith
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [Nat.factorial_succ]
    push_cast
    rw [mul_assoc, mul_assoc, ← mul_assoc (((n + 1 - i : ℕ) : ℝ) / ((n : ℝ) + 1))]
    calc 1 / ((i : ℝ) + 1) * ((((n + 1 - i : ℕ) : ℝ) / ((n : ℝ) + 1)) * c n * b i n)
        ≤ 1 / ((i : ℝ) + 1) * (1 / (i.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 1 / (((i : ℝ) + 1) * (i.factorial : ℝ)) := by
          rw [one_div_mul_one_div]

/-- Binomial moments: C(n-i,i) I(n-2i)/I(n) -> 1/i!. -/
theorem binom_moment_tendsto (i : ℕ) : Tendsto (fun n => b i n) atTop (𝓝 (1 / (i.factorial : ℝ))) := by
  induction i with
  | zero => simp [b_zero]
  | succ i ih =>
    rw [← tendsto_add_atTop_iff_nat 2]
    simp_rw [b_rec]
    have hq : Tendsto (fun n : ℕ => ((n + 1 - i : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (i : ℝ))
      rw [mul_zero, sub_zero] at h
      apply h.congr'
      filter_upwards [eventually_ge_atTop i] with n hn
      rw [Nat.cast_sub (by omega)]
      push_cast
      field_simp
    have := ((tendsto_const_nhds (x := 1 / ((i : ℝ) + 1))).mul hq).mul c_tendsto |>.mul ih
    convert this using 2
    rw [Nat.factorial_succ]
    push_cast
    field_simp

/-- The limit series: sum_i (-1)^(i+j) C(i,j)/i! = e^(-1)/j!. -/
theorem limit_hasSum (j : ℕ) :
    HasSum (fun i : ℕ => (-1 : ℝ) ^ (i + j) * (i.choose j : ℝ) * (1 / (i.factorial : ℝ)))
      (Real.exp (-1) / j.factorial) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_right (1 / (j.factorial : ℝ))
  rw [← hasSum_nat_add_iff' j]
  have hz : ∑ i ∈ range j, (-1 : ℝ) ^ (i + j) * (i.choose j : ℝ) * (1 / (i.factorial : ℝ)) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]
    simp
  rw [hz, sub_zero]
  convert h2 using 1
  · funext l
    have hc := Nat.add_choose_mul_factorial_mul_factorial l j
    rw [show l + j + j = l + (j + j) by ring, pow_add, Even.neg_one_pow ⟨j, rfl⟩,
      show (((l + j).factorial : ℕ) : ℝ) = ((l + j).choose j : ℝ) * l.factorial * j.factorial by
        exact_mod_cast hc.symm]
    have hl : (l.factorial : ℝ) ≠ 0 := by positivity
    have hj : (j.factorial : ℝ) ≠ 0 := by positivity
    have hcj : ((l + j).choose j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    field_simp
  · ring

theorem T_div_eq (n j : ℕ) :
    (T n j : ℝ) / I n = ∑' i, (-1 : ℝ) ^ (i + j) * (i.choose j : ℝ) * b i n := by
  rw [tsum_eq_sum (s := range (n + 1))]
  · unfold T b
    push_cast
    rw [sum_div]
    refine sum_congr rfl (fun i _ => ?_)
    ring
  · intro i hi
    rw [mem_range, not_lt] at hi
    rw [b_vanish i n (by omega), mul_zero]

/-- A217876 (Callan): T(n,j)/I(n) -> e^(-1)/j!, the Poisson(1) law. -/
theorem A217876_conjecture (j : ℕ) :
    Tendsto (fun n => (T n j : ℝ) / I n) atTop (𝓝 (Real.exp (-1) / j.factorial)) := by
  rw [← (limit_hasSum j).tsum_eq]
  simp_rw [T_div_eq]
  apply tendsto_tsum_of_dominated_convergence (bound := fun i => (i.choose j : ℝ) * (1 / (i.factorial : ℝ)))
  · apply Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (Real.summable_pow_div_factorial 2)
    have : ((i.choose j : ℕ) : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow i j
    push_cast at this
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right this (by positivity)
  · intro i
    exact tendsto_const_nhds.mul (binom_moment_tendsto i)
  · apply Eventually.of_forall
    intro n i
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (b_nonneg i n)]
    exact mul_le_mul_of_nonneg_left (b_le i n) (by positivity)

end A217876

open A217876
