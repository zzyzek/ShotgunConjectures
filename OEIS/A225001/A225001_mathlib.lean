/-
OEIS A225001, Mathlib proof.

A225001's program defines a(n) = floor(1/frac((e^(4/5))^(1/n))).
Main theorem `A225001_main`: for every n ≥ 2,
  ⌊1 / Int.fract (exp(4/5) ^ (1/n))⌋ = ⌊(5n - 2)/4⌋ = A047203(n),
the right side written as the natural-number quotient (5n - 2) / 4. This is
Mathar's conjecture a(n) = A047203(n) for n > 1 (README result).

Proof: u = 4/(5n) ∈ (0, 2/5]. From Mathlib's Taylor bounds
1 + u + u^2/2 ≤ e^u ≤ 1 + u + u^2/2 + 2u^3/9 one gets 1 ≤ e^u < 2 (so
frac(e^u) = e^u - 1) and
  (5n - 2)/4 = 1/u - 1/2 ≤ 1/(e^u - 1) < 1/u - 1/4;
as (5n - 2)/4 has fractional part ≤ 3/4, the floor is ⌊(5n - 2)/4⌋.

Not checked: nothing.
-/
import Mathlib

theorem A225001_main (n : ℕ) (hn : 2 ≤ n) :
    ⌊1 / Int.fract (Real.exp (4 / 5) ^ (1 / (n : ℝ)))⌋ = (((5 * n - 2) / 4 : ℕ) : ℤ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set u : ℝ := 4 / (5 * n) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 2 / 5 := by
    rw [hu, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hE : Real.exp (4 / 5) ^ (1 / (n : ℝ)) = Real.exp u := by
    rw [← Real.exp_mul, hu]
    congr 1
    field_simp
  rw [hE]
  set E := Real.exp u with hEdef
  have hlo : 1 + u + u ^ 2 / 2 ≤ E := Real.quadratic_le_exp_of_nonneg hu0.le
  have hup : E ≤ 1 + u + u ^ 2 / 2 + 2 / 9 * u ^ 3 := by
    have := Real.exp_bound' hu0.le (by linarith) (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  have hfl : ⌊E⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast; nlinarith
    · push_cast; nlinarith
  have hfr : Int.fract E = E - 1 := by
    rw [← Int.self_sub_floor, hfl]
    simp
  rw [hfr]
  have hE1 : 0 < E - 1 := by nlinarith
  -- 1/(e^u - 1) lies in [1/u - 1/2, 1/u - 1/4).
  --
  have hA : (2 - u) * (E - 1) ≤ 2 * u := by
    have h1 : (2 - u) * (E - 1) ≤ (2 - u) * (u + u ^ 2 / 2 + 2 / 9 * u ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [pow_pos hu0 3, pow_pos hu0 4]
  have hB : 4 * u < (4 - u) * (E - 1) := by
    have h1 : (4 - u) * (u + u ^ 2 / 2) ≤ (4 - u) * (E - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [pow_pos hu0 2, pow_pos hu0 3]
  have hq : ((5 * (n : ℝ) - 2) / 4) = (2 - u) / (2 * u) := by
    rw [hu]
    field_simp
    ring
  have hX1 : (5 * (n : ℝ) - 2) / 4 ≤ 1 / (E - 1) := by
    rw [hq, div_le_div_iff₀ (by positivity) hE1]
    linarith
  have hX2 : 1 / (E - 1) < (5 * (n : ℝ) - 2) / 4 + 1 / 4 := by
    rw [hq, show (2 - u) / (2 * u) + 1 / 4 = (4 - u) / (4 * u) by field_simp; ring,
      div_lt_div_iff₀ hE1 (by positivity)]
    linarith
  set q := (5 * n - 2) / 4 with hqdef
  have hq1 : 4 * q ≤ 5 * n - 2 := Nat.mul_div_le _ _
  have hq2 : 5 * n - 2 < 4 * q + 4 := by omega
  have hcast : ((5 * n - 2 : ℕ) : ℝ) = 5 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hr1 : (4 * q : ℝ) ≤ 5 * (n : ℝ) - 2 := by
    rw [← hcast]; exact_mod_cast hq1
  have hr2 : 5 * (n : ℝ) - 2 + 1 ≤ 4 * q + 4 := by
    rw [← hcast]; exact_mod_cast hq2
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> linarith
