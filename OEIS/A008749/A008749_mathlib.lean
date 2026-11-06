/-
OEIS A008749: expansion of (1+x^6)/((1-x)(1-x^2)(1-x^3)).
Conjecture (W. C. Yang, 2002, in the entry): for n >= 1, A067628(a(n+2))
appears for the first time in A067628, A067628 = minimal perimeter of a
polyiamond with T triangles.

Definitions.
* `a : ℕ → ℤ`: 1, 1, 2, 3, 4, 5 and a(n+6) = a(n+5) + a(n+4) - a(n+2)
  - a(n+1) + a(n) + [n = 0]; `A008749_gf` shows its generating function is
  (1+x^6)/((1-x)(1-x^2)(1-x^3)), i.e. mk a * (1-x)(1-x^2)(1-x^3) = 1 + x^6.
* `p T = 2 ⌈(T + √(6T))/2⌉ - T`: the Harary-Harborth (1976) formula for
  A067628 (stated in the entry's FORMULA section).

Main theorems.
* `A008749_gf`: the generating function.
* `six_a`: 6 a(n) = n^2 + e(n mod 6), e = 12, 5, 8, 9, 8, 5, for n >= 1;
  and a(n) ≡ n (mod 2).
* `p_eq_iff`: for T ≥ 1, v ≥ 2: p T = v ↔ v ≡ T (mod 2) ∧ (v-2)^2 < 6T ≤ v^2.
* `A008749_first`: for n ≥ 1, p(a(n+2)) = n + 4, and p(T) ≠ n + 4 for every
  T < a(n+2); so a(n+2) is the first index at which the value p(a(n+2))
  appears.

Not checked in this file: that p is the minimal polyiamond perimeter (the
Harary-Harborth theorem; geometric, not formalised here).
-/
import Mathlib

open PowerSeries

namespace A008749

def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | n + 6 => a (n + 5) + a (n + 4) - a (n + 2) - a (n + 1) + a n + (if n = 0 then 1 else 0)

theorem A008749_gf :
    PowerSeries.mk a * ((1 - X) * (1 - X ^ 2) * (1 - X ^ 3)) = 1 + X ^ 6 := by
  have hQ : ((1 : PowerSeries ℤ) - X) * (1 - X ^ 2) * (1 - X ^ 3) =
      1 - X - X ^ 2 + X ^ 4 + X ^ 5 - X ^ 6 := by ring
  rw [hQ]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
    coeff_one, coeff_X_pow]
  rw [show (PowerSeries.mk a * X) = PowerSeries.mk a * X ^ 1 by rw [pow_one], coeff_mul_X_pow']
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> simp [a]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega,
      show k + 6 - 6 = k by omega, a]
    by_cases hk : k = 0
    · subst hk; simp; ring
    · simp [hk]; ring

def e : ℕ → ℤ
  | 0 => 12
  | 1 => 5
  | 2 => 8
  | 3 => 9
  | 4 => 8
  | _ => 5

lemma e_bounds (r : ℕ) : 5 ≤ e r ∧ e r ≤ 12 := by
  unfold e; split <;> norm_num

theorem six_a (n : ℕ) (hn : 1 ≤ n) :
    6 * a n = (n : ℤ) ^ 2 + e (n % 6) ∧ (a n - n) % 2 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 7 with h | h
    · interval_cases n <;> simp [a, e]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have h0 := ih k (by omega) (by omega)
      have h1 := ih (k + 1) (by omega) (by omega)
      have h2 := ih (k + 2) (by omega) (by omega)
      have h4 := ih (k + 4) (by omega) (by omega)
      have h5 := ih (k + 5) (by omega) (by omega)
      have hk : k ≠ 0 := by omega
      rw [show a (k + 6) = a (k + 5) + a (k + 4) - a (k + 2) - a (k + 1) + a k by
        simp [a, hk]]
      push_cast at h0 h1 h2 h4 h5 ⊢
      refine ⟨?_, by omega⟩
      have hr : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
      rw [Nat.add_mod] at h1 h2 h4 h5 ⊢
      interval_cases hm : k % 6 <;> simp [e] at h0 h1 h2 h4 h5 ⊢ <;>
        linear_combination h5.1 + h4.1 - h2.1 - h1.1 + h0.1

/-- Harary-Harborth formula for A067628 (minimal perimeter of a T-polyiamond). -/
noncomputable def p (T : ℕ) : ℤ := 2 * ⌈((T : ℝ) + √(6 * T)) / 2⌉ - T

lemma p_zero : p 0 = 0 := by simp [p]

theorem p_eq_iff (T : ℕ) (v : ℤ) (hv : 2 ≤ v) :
    p T = v ↔ (v - T) % 2 = 0 ∧ (v - 2) ^ 2 < 6 * T ∧ 6 * (T : ℤ) ≤ v ^ 2 := by
  set s := √(6 * (T : ℝ)) with hs
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have s2 : s ^ 2 = 6 * T := Real.sq_sqrt (by positivity)
  have hvr : (2 : ℝ) ≤ v := by exact_mod_cast hv
  unfold p
  rw [← hs]
  constructor
  · intro h
    set k := ⌈((T : ℝ) + s) / 2⌉ with hk
    have c1 := Int.le_ceil (((T : ℝ) + s) / 2)
    have c2 := Int.ceil_lt_add_one (((T : ℝ) + s) / 2)
    rw [← hk] at c1 c2
    have hvk : (v : ℝ) = 2 * k - T := by rw [← h]; push_cast; ring
    refine ⟨by omega, ?_, ?_⟩
    · have : ((v - 2) ^ 2 : ℝ) < 6 * T := by
        rw [← s2]
        have : (v : ℝ) - 2 < s := by linarith
        nlinarith
      exact_mod_cast this
    · have : (6 * T : ℝ) ≤ v ^ 2 := by
        rw [← s2]
        have : s ≤ (v : ℝ) := by linarith
        nlinarith
      exact_mod_cast this
  · rintro ⟨hpar, h1, h2⟩
    obtain ⟨t, ht⟩ : ∃ t, v - T = 2 * t := ⟨(v - T) / 2, by omega⟩
    have r1 : ((v : ℝ) - 2) ^ 2 < 6 * T := by exact_mod_cast h1
    have r2 : (6 * T : ℝ) ≤ v ^ 2 := by exact_mod_cast h2
    have l1 : (v : ℝ) - 2 < s := by nlinarith
    have l2 : s ≤ (v : ℝ) := by nlinarith
    have htr : (v : ℝ) - T = 2 * t := by exact_mod_cast ht
    have hc : ⌈((T : ℝ) + s) / 2⌉ = t + T := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith
    rw [hc]; omega

/-- Yang's conjecture: a(n+2) is the first index where A067628 takes the value
A067628(a(n+2)) = n + 4. -/
theorem A008749_first (n : ℕ) (hn : 1 ≤ n) :
    p (a (n + 2)).toNat = n + 4 ∧ ∀ T : ℕ, (T : ℤ) < a (n + 2) → p T ≠ n + 4 := by
  obtain ⟨hA, hpar⟩ := six_a (n + 2) (by omega)
  obtain ⟨e1, e2⟩ := e_bounds ((n + 2) % 6)
  set A := a (n + 2) with hAdef
  set E := e ((n + 2) % 6)
  push_cast at hA hpar
  have hApos : 0 ≤ A := by nlinarith
  have hv : (2 : ℤ) ≤ n + 4 := by omega
  constructor
  · rw [p_eq_iff _ _ hv, Int.toNat_of_nonneg hApos]
    refine ⟨by omega, by nlinarith, by nlinarith⟩
  · intro T hT hpT
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · subst h0; rw [p_zero] at hpT; omega
    · rw [p_eq_iff _ _ hv] at hpT
      obtain ⟨hp1, hp2, _⟩ := hpT
      have hT2 : (T : ℤ) + 2 ≤ A := by omega
      nlinarith
