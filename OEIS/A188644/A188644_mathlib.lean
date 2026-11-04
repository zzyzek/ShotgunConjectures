/-
OEIS A188644, conjecture (C. Hohn): with k = ((x^2 + y)^(1/2) + x)^2, x ≥ 1
an integer and y = ±1, ((k^n) + (k^(-n)))/2 is always an integer; this entry
is y = -1.

Main theorem `A188644_conjecture`: for every natural x ≥ 1 and n, with
k = (√(x² − 1) + x)² (real square root), (k^n + k^(-n))/2 equals the integer
T_n(2x² − 1), T_n the Chebyshev polynomial of the first kind over ℤ (Mathlib
`Polynomial.Chebyshev.T`).  `A188644_integer` restates this as membership in ℤ.
This is the README result.  The core lemma `hohnK_pow_add` covers both signs
y = ±1 (y = 1 is OEIS A188645).

Proof: k·(√(x²+y) − x)² = y² = 1, so k^(-1) = (√(x²+y) − x)² and
k + k^(-1) = 2(2x² + y); then u_n = k^n + k^(-n) satisfies
u_(n+2) = 2(2x²+y)·u_(n+1) − u_n, the Chebyshev recurrence.

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

theorem A188644_conjecture (x : ℕ) (hx : 1 ≤ x) (n : ℕ) :
    let k : ℝ := (Real.sqrt ((x : ℝ) ^ 2 - 1) + x) ^ 2
    (k ^ (n : ℤ) + k ^ (-(n : ℤ))) / 2 =
      (((Chebyshev.T ℤ n).eval (2 * (x : ℤ) ^ 2 - 1) : ℤ) : ℝ) := by
  intro k
  have h := hohnK_pow_add x hx (-1) (Or.inr rfl) n
  have hk : k = hohnK x (-1) := by
    simp only [k, hohnK]; push_cast; ring_nf
  rw [hk, zpow_neg, zpow_natCast, ← inv_pow, h]
  simp [sub_eq_add_neg]

theorem A188644_integer (x : ℕ) (hx : 1 ≤ x) (n : ℕ) :
    ∃ z : ℤ, let k : ℝ := (Real.sqrt ((x : ℝ) ^ 2 - 1) + x) ^ 2
      (k ^ (n : ℤ) + k ^ (-(n : ℤ))) / 2 = z :=
  ⟨_, A188644_conjecture x hx n⟩
