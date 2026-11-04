/-
OEIS A188646, conjecture (C. Hohn): with k = ((x^2 + y)^(1/2) + x)^2 and
a(0) = 1, for all integers x ≥ 1 and y = ±1 the sequence
a(n) = a(n-1)·k − (k−1)/k^n consists of integers; this entry is y = -1
(A188647 is y = 1).

Main theorem `A188646_conjecture`: for every natural x ≥ 1, y ∈ {1, -1} and
n, the real number `hohnSeq (hohnK x y) n` is an integer, where
hohnK x y = (√(x² + y) + x)² and hohnSeq k is the recurrence above
(a 0 = 1, a (n+1) = a n · k − (k−1)/k^(n+1)).  `A188646_entry` is the
special case y = -1 written out.  This is the README result (both signs).

Proof: (k+1)·a(n) = k^(n+1) + k^(-n) by induction; the integer sequence
c(0) = 1, c(n+1) = −c(n) + 2·T_(n+1)(2x²+y) satisfies the same identity
because k^j + k^(-j) = 2·T_j(2x²+y) (`hohnK_pow_add`, Chebyshev polynomials);
k + 1 ≠ 0, so a = c.

Not checked: nothing outside Lean.
-/
import Mathlib

open Polynomial

/-- Hohn's constant k = (√(x² + y) + x)². -/
noncomputable def hohnK (x : ℕ) (y : ℤ) : ℝ := (Real.sqrt ((x : ℝ) ^ 2 + y) + x) ^ 2

lemma hohnK_facts (x : ℕ) (hx : 1 ≤ x) (y : ℤ) (hy : y = 1 ∨ y = -1) :
    hohnK x y ≠ 0 ∧ hohnK x y * (hohnK x y)⁻¹ = 1 ∧
      hohnK x y + (hohnK x y)⁻¹ = 2 * ((2 * (x : ℤ) ^ 2 + y : ℤ) : ℝ) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hy2 : (y : ℝ) ^ 2 = 1 := by rcases hy with rfl | rfl <;> norm_num
  have hy1 : (-1 : ℝ) ≤ y := by rcases hy with rfl | rfl <;> norm_num
  have hpos : (0 : ℝ) ≤ (x : ℝ) ^ 2 + y := by nlinarith
  set s := Real.sqrt ((x : ℝ) ^ 2 + y) with hsdef
  have hs : s ^ 2 = (x : ℝ) ^ 2 + y := Real.sq_sqrt hpos
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hk0 : hohnK x y ≠ 0 := by
    unfold hohnK; rw [← hsdef]; positivity
  have hprod : hohnK x y * (s - x) ^ 2 = 1 := by
    unfold hohnK; rw [← hsdef]
    have : (s + x) ^ 2 * (s - x) ^ 2 = (s ^ 2 - (x : ℝ) ^ 2) ^ 2 := by ring
    rw [this, hs]; linear_combination hy2
  have hinv : (hohnK x y)⁻¹ = (s - x) ^ 2 := inv_eq_of_mul_eq_one_right hprod
  refine ⟨hk0, mul_inv_cancel₀ hk0, ?_⟩
  rw [hinv]; unfold hohnK; rw [← hsdef]; push_cast
  linear_combination 2 * hs

/-- k^n + k^(-n) = 2·T_n(2x² + y), with T_n the Chebyshev polynomial over ℤ. -/
lemma hohnK_pow_add (x : ℕ) (hx : 1 ≤ x) (y : ℤ) (hy : y = 1 ∨ y = -1) (n : ℕ) :
    hohnK x y ^ n + (hohnK x y)⁻¹ ^ n =
      2 * (((Chebyshev.T ℤ n).eval (2 * (x : ℤ) ^ 2 + y) : ℤ) : ℝ) := by
  obtain ⟨_, hkk, hsum⟩ := hohnK_facts x hx y hy
  set k := hohnK x y
  set k' := (hohnK x y)⁻¹
  set m : ℤ := 2 * (x : ℤ) ^ 2 + y
  have key : ∀ n : ℕ, (k ^ n + k' ^ n = 2 * (((Chebyshev.T ℤ n).eval m : ℤ) : ℝ)) ∧
      (k ^ (n + 1) + k' ^ (n + 1) = 2 * (((Chebyshev.T ℤ (n + 1 : ℕ)).eval m : ℤ) : ℝ)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp; norm_num, ?_⟩
      simp only [zero_add, pow_one, Nat.cast_one, Chebyshev.T_one, eval_X]
      exact hsum
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hT : Chebyshev.T ℤ ((n + 1 + 1 : ℕ) : ℤ) =
          2 * X * Chebyshev.T ℤ ((n + 1 : ℕ) : ℤ) - Chebyshev.T ℤ (n : ℤ) := by
        have h2 := Chebyshev.T_add_two ℤ (n : ℤ)
        push_cast
        rw [show (n : ℤ) + 1 + 1 = n + 2 by ring, h2]
      rw [hT]
      simp only [eval_sub, eval_mul, eval_X, eval_ofNat, Int.cast_sub, Int.cast_mul,
        Int.cast_ofNat]
      have e1 := ih.1
      have e2 := ih.2
      linear_combination (k + k') * e2 - (k * k') * e1 +
        2 * (((Chebyshev.T ℤ (n + 1 : ℕ)).eval m : ℤ) : ℝ) * hsum -
        2 * (((Chebyshev.T ℤ (n : ℕ)).eval m : ℤ) : ℝ) * hkk
  exact (key n).1

/-- a(0) = 1, a(n) = a(n−1)·k − (k−1)/k^n. -/
noncomputable def hohnSeq (k : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => hohnSeq k n * k - (k - 1) / k ^ (n + 1)

/-- The integer companion c(0) = 1, c(n+1) = −c(n) + 2·T_(n+1)(2x²+y). -/
noncomputable def hohnInt (x : ℕ) (y : ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => -hohnInt x y n + 2 * (Chebyshev.T ℤ (n + 1 : ℕ)).eval (2 * (x : ℤ) ^ 2 + y)

theorem A188646_conjecture (x : ℕ) (hx : 1 ≤ x) (y : ℤ) (hy : y = 1 ∨ y = -1) (n : ℕ) :
    ∃ z : ℤ, hohnSeq (hohnK x y) n = z := by
  obtain ⟨hk0, hkk, _⟩ := hohnK_facts x hx y hy
  have hTall := hohnK_pow_add x hx y hy
  set k := hohnK x y
  set k' := (hohnK x y)⁻¹
  have hkpos : 0 < k := by
    simp only [k, hohnK]
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have := Real.sqrt_nonneg ((x : ℝ) ^ 2 + y)
    positivity
  have hk1 : k + 1 ≠ 0 := by linarith
  have ha : ∀ n, (k + 1) * hohnSeq k n = k ^ (n + 1) + k' ^ n := by
    intro n
    induction n with
    | zero => simp [hohnSeq]
    | succ n ih =>
      simp only [hohnSeq, div_eq_mul_inv, ← inv_pow]
      linear_combination k * ih - k * k' ^ n * hkk
  have hc : ∀ n, (k + 1) * (hohnInt x y n : ℝ) = k ^ (n + 1) + k' ^ n := by
    intro n
    induction n with
    | zero => simp [hohnInt]
    | succ n ih =>
      have hT := hTall (n + 1)
      simp only [hohnInt, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_ofNat]
      linear_combination -ih - (k + 1) * hT + k' ^ n * hkk
  refine ⟨hohnInt x y n, ?_⟩
  apply mul_left_cancel₀ hk1
  rw [ha, hc]

theorem A188646_entry (x : ℕ) (hx : 1 ≤ x) (n : ℕ) :
    ∃ z : ℤ, hohnSeq ((Real.sqrt ((x : ℝ) ^ 2 - 1) + x) ^ 2) n = z := by
  have hk : (Real.sqrt ((x : ℝ) ^ 2 - 1) + x) ^ 2 = hohnK x (-1) := by
    simp only [hohnK]; push_cast; ring_nf
  rw [hk]
  exact A188646_conjecture x hx (-1) (Or.inr rfl) n
