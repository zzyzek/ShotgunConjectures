/-
OEIS A188647 (Hohn's conjecture), Mathlib proof.

For an integer x ≥ 1 and y = ±1 put k = (√(x^2 + y) + x)^2 (a real number)
and a(0) = 1, a(n) = a(n-1) k - (k - 1)/k^n.

Main theorem `A188647_main`: for every x ≥ 1, y ∈ {1, -1} and n, a(n) is an
integer. The entry A188647 is y = 1; the theorem covers both signs of
Hohn's claim (y = -1 is A188646).

Proof: with 1/k = (√(x^2 + y) - x)^2 one has a(n) (k + 1) = k^(n+1) + k^(-n),
w(n) = k^n + k^(-n) is an integer sequence (w(0) = 2, w(1) = 2(2x^2 + y),
w(n+2) = w(1) w(n+1) - w(n)), and a(n) = w(n) - a(n-1).

Not checked: nothing.
-/
import Mathlib

/-- Hohn's sequence over ℝ. -/
noncomputable def A188647_a (k : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => A188647_a k n * k - (k - 1) / k ^ (n + 1)

/-- The integer sequence w(n) = k^n + k^(-n). -/
def A188647_w (c : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => c
  | n + 2 => c * A188647_w c (n + 1) - A188647_w c n

/-- The integer sequence equal to a(n). -/
def A188647_A (c : ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => A188647_w c (n + 1) - A188647_A c n

theorem A188647_closed (k j : ℝ) (hkj : k * j = 1) (n : ℕ) :
    A188647_a k n * (k + 1) = k ^ (n + 1) + j ^ n := by
  induction n with
  | zero => simp [A188647_a]
  | succ n ih =>
    simp only [A188647_a]
    have hinv : 1 / k ^ (n + 1) = j ^ (n + 1) := by
      rw [one_div, ← inv_pow, inv_eq_of_mul_eq_one_right hkj]
    rw [div_eq_mul_one_div, hinv]
    linear_combination k * ih - k * j ^ n * hkj

theorem A188647_main (x : ℕ) (hx : 1 ≤ x) (y : ℤ) (hy : y = 1 ∨ y = -1) (n : ℕ) :
    ∃ m : ℤ, A188647_a ((Real.sqrt ((x : ℝ) ^ 2 + y) + x) ^ 2) n = m := by
  set s := Real.sqrt ((x : ℝ) ^ 2 + y) with hs
  have hpos : (0 : ℝ) ≤ (x : ℝ) ^ 2 + y := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    rcases hy with rfl | rfl <;> push_cast <;> nlinarith
  have hs2 : s ^ 2 = (x : ℝ) ^ 2 + y := Real.sq_sqrt hpos
  have hy2 : (y : ℝ) ^ 2 = 1 := by rcases hy with rfl | rfl <;> norm_num
  set k := (s + x) ^ 2 with hk
  set j := (s - x) ^ 2 with hj
  have hkj : k * j = 1 := by
    have : k * j = (s ^ 2 - (x : ℝ) ^ 2) ^ 2 := by rw [hk, hj]; ring
    rw [this, hs2]
    simpa using hy2
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, zero_mul] at hkj
    exact zero_ne_one hkj
  have hk1 : k + 1 ≠ 0 := by
    have : 0 ≤ k := sq_nonneg _
    linarith
  set c : ℤ := 2 * (2 * x ^ 2 + y) with hc
  have hck : (c : ℝ) = k + j := by
    rw [hc, hk, hj]
    push_cast
    nlinarith [hs2]
  -- w(n) = k^n + j^n.
  --
  have hw : ∀ n, (A188647_w c n : ℝ) = k ^ n + j ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simp [A188647_w]; norm_num
      | 1, _ => simp [A188647_w, hck]
      | m + 2, ih =>
        simp only [A188647_w]
        push_cast
        rw [ih (m + 1) (by omega), ih m (by omega), hck]
        have : k ^ (m + 1) * j = k ^ m * (k * j) := by ring
        have h2 : k * j ^ (m + 1) = j ^ m * (k * j) := by ring
        linear_combination (k ^ m + j ^ m) * hkj
  -- Both a and A satisfy x(n) (k + 1) = k^(n+1) + j^n.
  --
  have ha := A188647_closed k j hkj
  have hA : ∀ n, (A188647_A c n : ℝ) * (k + 1) = k ^ (n + 1) + j ^ n := by
    intro n
    induction n with
    | zero => simp [A188647_A]
    | succ n ih =>
      simp only [A188647_A]
      push_cast
      rw [hw]
      linear_combination -ih + j ^ n * hkj
  refine ⟨A188647_A c n, ?_⟩
  have := (ha n).trans (hA n).symm
  exact mul_right_cancel₀ hk1 this
