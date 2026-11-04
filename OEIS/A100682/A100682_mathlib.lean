/-
OEIS A100682, Mathlib proof.

Conjecture (Greathouse, 2012): floor((n - 3/2)/24^(1/4)) equals
floor(C(n,4)^(1/4)) except for n in {0, 1, 6, 17, 2403, 5318}.
Reading (README): the entry defines a(n) = floor(C(n+3,4)^(1/4)); the
conjecture's exception list matches the indexing floor(C(n,4)^(1/4)), so
that is the function compared here (OEIS index n - 3).

Main theorem `A100682_main`: for n = 634027531 (not in the exception list),
  ⌊(C(n,4) : ℝ)^(1/4)⌋ = 286454272  and  ⌊((n : ℝ) - 3/2)/24^(1/4)⌋ = 286454273,
with real powers (`Real.rpow`) and `Int.floor`. So the exception list is
incomplete, the README result. The real step (monotonicity of x ↦ x^4 on
x ≥ 0) is proved here; nothing is outside Lean.
-/
import Mathlib

/-- For r ≥ 0: ⌊r⌋ = b iff b^4 ≤ r^4 < (b+1)^4. -/
theorem A100682_floor_of_pow4 (r : ℝ) (hr : 0 ≤ r) (b : ℕ)
    (h1 : (b : ℝ) ^ 4 ≤ r ^ 4) (h2 : r ^ 4 < ((b : ℝ) + 1) ^ 4) : ⌊r⌋ = b := by
  rw [Int.floor_eq_iff]
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  constructor
  · push_cast
    exact (pow_le_pow_iff_left₀ hb hr (by norm_num)).1 h1
  · push_cast
    exact (pow_lt_pow_iff_left₀ hr (by positivity) (by norm_num)).1 h2

theorem A100682_rpow4 (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem A100682_main :
    (634027531 : ℕ) ∉ ({0, 1, 6, 17, 2403, 5318} : Finset ℕ) ∧
    ⌊(((634027531 : ℕ).choose 4 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋ = 286454272 ∧
    ⌊(((634027531 : ℕ) : ℝ) - 3 / 2) / (24 : ℝ) ^ ((1 : ℝ) / 4)⌋ = 286454273 := by
  have hc : (634027531 : ℕ).choose 4 =
      634027531 * 634027530 * 634027529 * 634027528 / 24 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  refine ⟨by decide, ?_, ?_⟩
  · have hC : (0 : ℝ) ≤ (((634027531 : ℕ).choose 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    apply A100682_floor_of_pow4 _ (Real.rpow_nonneg hC _)
    · rw [A100682_rpow4 _ hC, hc]; norm_num
    · rw [A100682_rpow4 _ hC, hc]; norm_num
  · have hs : (0 : ℝ) < (24 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    have hs4 := A100682_rpow4 24 (by norm_num)
    apply A100682_floor_of_pow4 _ (div_nonneg (by norm_num) hs.le)
    · rw [div_pow, hs4]; norm_num
    · rw [div_pow, hs4]; norm_num
