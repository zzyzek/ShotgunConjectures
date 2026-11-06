/-
OEIS A098021, Mathlib proof that the former and the current definitions agree.

Current definition (C. Kimberling): positions of 0's in the zero-one sequence
[n*r+2*r]-[n*r]-[2*r], r = sqrt(2), [ ] = floor  (`A098021_new n`).
Former definition (R. L. Bagula, history rev. #25): f(n) = n*sqrt(2) mod 1,
g(x) = -1 on [0,1/3], 0 on (1/3,2/3], 1 on (2/3,1]; n is a term when
f(n+2) - 2 f(n+1) + f(n) - g(f(n+1)) = 0  (`A098021_old n`). The FORMULA field wrote
"1/3 < x <= 1" for the last case, an evident typo for the 2/3 used in the Mathematica
program; `g` below tests the cases in order, so both readings give the same function.

Main theorems.
- `A098021_defs_agree`: for every integer n, A098021_old n ↔ A098021_new n.
- `A098021_old_eq_new`: the two sequences (positive n, in increasing order, as `Nat.nth`)
  are equal.
Both conditions are equivalent to frac(n·sqrt 2) < 3 - 2 sqrt 2; irrationality is not used.

Not checked in Lean: the listed terms (certificate/check_A098021.py compares them).
-/
import Mathlib

open Real

/-- f(n) = n·√2 mod 1. -/
noncomputable def A098021_f (n : ℤ) : ℝ := Int.fract ((n : ℝ) * √2)

/-- g(x) = -1 for x ≤ 1/3, 0 for 1/3 < x ≤ 2/3, 1 otherwise. -/
noncomputable def A098021_g (x : ℝ) : ℝ := if x ≤ 1 / 3 then -1 else if x ≤ 2 / 3 then 0 else 1

/-- Former definition: f(n+2) - 2 f(n+1) + f(n) - g(f(n+1)) = 0. -/
def A098021_old (n : ℤ) : Prop :=
  A098021_f (n + 2) - 2 * A098021_f (n + 1) + A098021_f n - A098021_g (A098021_f (n + 1)) = 0

/-- Current definition: [n r + 2 r] - [n r] - [2 r] = 0 with r = √2. -/
def A098021_new (n : ℤ) : Prop := ⌊(n : ℝ) * √2 + 2 * √2⌋ - ⌊(n : ℝ) * √2⌋ - ⌊2 * √2⌋ = 0

theorem A098021_key (y : ℝ) :
    (Int.fract (y + 2 * √2) - 2 * Int.fract (y + √2) + Int.fract y
        - A098021_g (Int.fract (y + √2)) = 0) ↔
      (⌊y + 2 * √2⌋ - ⌊y⌋ - ⌊2 * √2⌋ = 0) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hs0 := Real.sqrt_nonneg 2
  have hss := Real.sq_sqrt h2
  have hs1 : (1.41 : ℝ) < √2 := by nlinarith
  have hs2 : √2 < (1.42 : ℝ) := by nlinarith
  have hfl2 : ⌊2 * √2⌋ = 2 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hF1 := Int.floor_le y
  have hF2 := Int.lt_floor_add_one y
  simp only [Int.fract]
  rw [hfl2]
  obtain ⟨F, hF⟩ : ∃ F, ⌊y⌋ = F := ⟨_, rfl⟩
  rw [hF] at hF1 hF2 ⊢
  rcases lt_or_ge (y - F) (3 - 2 * √2) with hA | hA
  · have e1 : ⌊y + √2⌋ = F + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have e2 : ⌊y + 2 * √2⌋ = F + 2 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [e1, e2]
    push_cast
    have hg : A098021_g (y + √2 - (F + 1)) = 0 := by
      unfold A098021_g
      split_ifs <;> linarith
    rw [hg]
    exact iff_of_true (by ring) (by omega)
  rcases lt_or_ge (y - F) (2 - √2) with hB | hB
  · have e1 : ⌊y + √2⌋ = F + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have e2 : ⌊y + 2 * √2⌋ = F + 3 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [e1, e2]
    push_cast
    refine iff_of_false (fun h => ?_) (by omega)
    unfold A098021_g at h
    split_ifs at h <;> linarith
  · have e1 : ⌊y + √2⌋ = F + 2 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have e2 : ⌊y + 2 * √2⌋ = F + 3 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [e1, e2]
    push_cast
    refine iff_of_false (fun h => ?_) (by omega)
    unfold A098021_g at h
    split_ifs at h <;> linarith

/-- The former and the current definitions select the same integers. -/
theorem A098021_defs_agree (n : ℤ) : A098021_old n ↔ A098021_new n := by
  unfold A098021_old A098021_new A098021_f
  rw [show ((n + 2 : ℤ) : ℝ) * √2 = (n : ℝ) * √2 + 2 * √2 by push_cast; ring,
    show ((n + 1 : ℤ) : ℝ) * √2 = (n : ℝ) * √2 + √2 by push_cast; ring]
  exact A098021_key _

/-- The sequences (positive terms in increasing order) are equal. -/
theorem A098021_old_eq_new :
    Nat.nth (fun n : ℕ => 0 < n ∧ A098021_old n) = Nat.nth (fun n : ℕ => 0 < n ∧ A098021_new n) := by
  congr 1
  funext n
  rw [A098021_defs_agree]

