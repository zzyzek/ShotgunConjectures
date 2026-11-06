import Mathlib

/-
OEIS A136269 (offset 0): a(n) = floor of the sum of the first 10^n cube roots,
a(n) = floor(Sum_{i=1..10^n} i^(1/3)).
Conjecture (entry): for n = 3k, a(n) = (3/4)*10^(4n/3) + 5*10^(n/3-1) - 1.
The formula is not an integer for k = 0 (a(0) = 1), so the claim is for k ≥ 1.

Definitions.  `cr i = (i : ℝ) ^ (1/3 : ℝ)` (real cube root), `S N = Σ_{i<N} cr (i+1)`,
`A136269 n = ⌊S (10^n)⌋`.

Main theorems.
* `A136269_conj`: for k ≥ 1, (A136269 (3k) : ℝ) = 3/4 * 10^(4k) + 5 * 10^(k-1) - 1.
* `floor_sum_cube_even`: for every even M ≥ 2,
  ⌊Σ_{i=1..M^3} i^(1/3)⌋ = 3M^4/4 + M/2 - 1.
* `sum_bounds`: for every N ≥ 1, with c = N^(1/3) and H = 3/4 c^4 + 1/2 c,
  H - 1/4 - 1/36 (1 - 1/c^2) ≤ S N ≤ H - 1/4.

Route.  With a = (i-1)^(1/3), b = i^(1/3) (so b^3 - a^3 = 1), the trapezoid
excess E = H(b) - H(a) - b equals (b-a)^3 (a+b)/4 (`step`): it is positive,
equals 1/4 for i = 1, and is at most (1/a^2 - 1/b^2)/36 for i ≥ 2, because
(b-a) a b ≤ (b-a)(a^2+ab+b^2)/3 = 1/3.  Summing telescopes.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py evaluates the sums exactly for n ≤ 9 and the formula).
-/

namespace OEIS136269

/-- Real cube root of a natural number. -/
noncomputable def cr (i : ℕ) : ℝ := (i : ℝ) ^ ((1 : ℝ) / 3)

/-- Sum of the cube roots of 1, ..., N. -/
noncomputable def S (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, cr (i + 1)

/-- A136269: floor of the sum of the first 10^n cube roots. -/
noncomputable def A136269 (n : ℕ) : ℤ := ⌊S (10 ^ n)⌋

/-- The comparison function H(c) = 3/4 c^4 + 1/2 c. -/
noncomputable def H (c : ℝ) : ℝ := 3 / 4 * c ^ 4 + 1 / 2 * c

theorem cr_nonneg (i : ℕ) : 0 ≤ cr i := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem cr_cube (i : ℕ) : cr i ^ 3 = i := by
  unfold cr
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem cr_one : cr 1 = 1 := by simp [cr]

theorem cr_pow3 (M : ℕ) : cr (M ^ 3) = M := by
  unfold cr
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem cr_lt (i : ℕ) : cr i < cr (i + 1) := by
  unfold cr
  exact Real.rpow_lt_rpow (Nat.cast_nonneg _) (by push_cast; linarith) (by norm_num)

theorem one_le_cr (i : ℕ) (hi : 1 ≤ i) : 1 ≤ cr i := by
  rw [← cr_one]
  unfold cr
  exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hi) (by norm_num)

/-- The trapezoid excess for one step of the cube-root sum. -/
theorem step (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (h : b ^ 3 - a ^ 3 = 1) :
    0 < H b - H a - b ∧ (1 ≤ a → H b - H a - b ≤ 1 / 36 * (1 / a ^ 2 - 1 / b ^ 2)) := by
  have hE : H b - H a - b = (b - a) ^ 3 * (a + b) / 4 := by
    unfold H
    linear_combination ((a + b) / 2) * h
  rw [hE]
  have hd : 0 < b - a := by linarith
  refine ⟨div_pos (mul_pos (pow_pos hd 3) (by linarith)) (by norm_num), fun ha1 => ?_⟩
  have hb1 : 1 < b := by linarith
  have h1 : (b - a) * (a ^ 2 + a * b + b ^ 2) = 1 := by linear_combination h
  have h2 : 3 * ((b - a) * (a * b)) ≤ 1 := by
    rw [← h1]
    have : 3 * (a * b) ≤ a ^ 2 + a * b + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    nlinarith
  have h0 : 0 ≤ 3 * ((b - a) * (a * b)) := by
    have : 0 ≤ a * b := by positivity
    nlinarith
  have h3 : 9 * ((b - a) ^ 2 * (a ^ 2 * b ^ 2)) ≤ 1 := by nlinarith
  have key : 1 / 36 * (1 / a ^ 2 - 1 / b ^ 2) = (b - a) * (a + b) / (36 * (a ^ 2 * b ^ 2)) := by
    field_simp
    ring
  rw [key, le_div_iff₀ (by positivity)]
  have hp : 0 ≤ (b - a) * (a + b) := mul_nonneg hd.le (by linarith)
  calc (b - a) ^ 3 * (a + b) / 4 * (36 * (a ^ 2 * b ^ 2))
      = ((b - a) * (a + b)) * (9 * ((b - a) ^ 2 * (a ^ 2 * b ^ 2))) := by ring
    _ ≤ ((b - a) * (a + b)) * 1 := mul_le_mul_of_nonneg_left h3 hp
    _ = (b - a) * (a + b) := by ring

theorem sum_bounds (N : ℕ) (hN : 1 ≤ N) :
    H (cr N) - 1 / 4 - 1 / 36 * (1 - 1 / cr N ^ 2) ≤ S N ∧ S N ≤ H (cr N) - 1 / 4 := by
  induction N, hN using Nat.le_induction with
  | base => simp [S, H, cr_one]; norm_num
  | succ N hN ih =>
    have hS : S (N + 1) = S N + cr (N + 1) := by simp [S, Finset.sum_range_succ]
    have h3 : cr (N + 1) ^ 3 - cr N ^ 3 = 1 := by rw [cr_cube, cr_cube]; push_cast; ring
    obtain ⟨hpos, hup⟩ := step (cr N) (cr (N + 1)) (cr_nonneg N) (cr_lt N) h3
    have hup' := hup (one_le_cr N hN)
    rw [hS]
    constructor <;> linarith [ih.1, ih.2]

theorem cube_bounds (M : ℕ) (hM : 1 ≤ M) :
    H M - 1 < S (M ^ 3) ∧ S (M ^ 3) ≤ H M - 1 / 4 := by
  have hb := sum_bounds (M ^ 3) (Nat.one_le_pow _ _ hM)
  rw [cr_pow3] at hb
  have : 0 ≤ 1 / (M : ℝ) ^ 2 := by positivity
  constructor <;> linarith [hb.1, hb.2]

/-- For even M ≥ 2 the floor of the sum of the cube roots of 1..M^3 is 3M^4/4 + M/2 - 1. -/
theorem floor_sum_cube_even (M : ℕ) (hM : 1 ≤ M) (he : Even M) :
    ((⌊S (M ^ 3)⌋ : ℤ) : ℝ) = 3 / 4 * (M : ℝ) ^ 4 + (M : ℝ) / 2 - 1 := by
  obtain ⟨t, rfl⟩ := he
  have hb := cube_bounds (t + t) hM
  have hz : ⌊S ((t + t) ^ 3)⌋ = 12 * (t : ℤ) ^ 4 + t - 1 := by
    rw [Int.floor_eq_iff]
    unfold H at hb
    push_cast at hb ⊢
    constructor <;> nlinarith [hb.1, hb.2]
  rw [hz]
  push_cast
  ring

/-- **A136269**: for n = 3k, k ≥ 1, a(n) = (3/4)*10^(4n/3) + 5*10^(n/3-1) - 1. -/
theorem A136269_conj (k : ℕ) (hk : 1 ≤ k) :
    (A136269 (3 * k) : ℝ) = 3 / 4 * (10 : ℝ) ^ (4 * k) + 5 * (10 : ℝ) ^ (k - 1) - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have he : Even (10 ^ (j + 1)) := (Nat.even_pow' (by omega)).2 (by decide)
  have h := floor_sum_cube_even (10 ^ (j + 1)) (Nat.one_le_pow _ _ (by norm_num)) he
  unfold A136269
  rw [show 10 ^ (3 * (j + 1)) = (10 ^ (j + 1)) ^ 3 by ring, h]
  push_cast
  ring

