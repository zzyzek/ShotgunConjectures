import Mathlib.Tactic

/-
FAM-goormaghtigh (Mathlib). Goormaghtigh's equation
(x^m - 1)/(x - 1) = (y^n - 1)/(y - 1), x > y > 1, n > m > 2, for the exponent pairs
(m, n) = (3, 5) and (3, 7). Both pairs are settled in the literature (Makowski-Schinzel for
n ≤ 5; Yuan 2005 for m = 3 and n odd); this file is a formalisation, not a new result.

Checked here:
* `goor35`: x^2 + x + 1 = y^4 + y^3 + y^2 + y + 1 over ℕ only for (x, y) = (0, 0), (5, 2).
* `goor35_repunit`: with y ≥ 2, repunit x 3 = repunit y 5 forces x = 5, y = 2 (the number 31).
* `goor37`: x^2 + x + 1 = y^6 + ... + y + 1 has no solution with y ≥ 2.
* `goor37_repunit`: the same in repunit form.
Method: Runge-type squeeze. 4(x^2 + x + 1) - 3 = (2x + 1)^2 lies strictly between two
consecutive squares of polynomials in y once y is past a small bound; the small y are
checked by `decide`.
`repunit` is the formal-conjectures definition (FormalConjectures/Wikipedia/Goormaghtigh.lean).
Outside Lean: nothing.
-/

/-- The repunit with `digits` digits in base `base` (as in formal-conjectures). -/
def repunit (base digits : ℕ) : ℕ :=
  ∑ i ∈ Finset.range digits, base ^ i

theorem goor35 (x y : ℕ) (h : x ^ 2 + x + 1 = y ^ 4 + y ^ 3 + y ^ 2 + y + 1) :
    (x = 0 ∧ y = 0) ∨ (x = 5 ∧ y = 2) := by
  -- For y ≥ 3, (2y^2 + y)^2 < (2x + 1)^2 < (2y^2 + y + 1)^2.
  --
  have hy : y ≤ 2 := by
    by_contra hy
    push Not at hy
    have h1 : 2 * y ^ 2 + y < 2 * x + 1 := by
      by_contra h1
      push Not at h1
      have := Nat.mul_le_mul h1 h1
      nlinarith
    have h2 : 2 * x + 1 < 2 * y ^ 2 + y + 1 := by
      by_contra h2
      push Not at h2
      have := Nat.mul_le_mul h2 h2
      nlinarith
    omega
  have key : ∀ y ∈ [0, 1, 2], ∀ x < 40, x ^ 2 + x + 1 = y ^ 4 + y ^ 3 + y ^ 2 + y + 1 →
      (x = 0 ∧ y = 0) ∨ (x = 5 ∧ y = 2) := by
    decide +kernel
  have hx : x < 40 := by
    interval_cases y <;> nlinarith
  exact key y (by interval_cases y <;> simp) x hx h

theorem goor35_repunit (x y : ℕ) (hy : 2 ≤ y) (h : repunit x 3 = repunit y 5) :
    x = 5 ∧ y = 2 := by
  have h' : x ^ 2 + x + 1 = y ^ 4 + y ^ 3 + y ^ 2 + y + 1 := by
    simp only [repunit, Finset.sum_range_succ, Finset.sum_range_zero] at h
    linarith
  rcases goor35 x y h' with h0 | h0
  · omega
  · exact h0

theorem goor37 (x y : ℕ) (hy : 2 ≤ y)
    (h : x ^ 2 + x + 1 = y ^ 6 + y ^ 5 + y ^ 4 + y ^ 3 + y ^ 2 + y + 1) : False := by
  -- With T = 8y^3 + 4y^2 + 3y and y ≥ 6: (T + 2)^2 < (4(2x + 1))^2 < (T + 3)^2.
  --
  have hy5 : y ≤ 5 := by
    by_contra hy5
    push Not at hy5
    have h1 : 8 * y ^ 3 + 4 * y ^ 2 + 3 * y + 2 < 4 * (2 * x + 1) := by
      by_contra h1
      push Not at h1
      have := Nat.mul_le_mul h1 h1
      nlinarith
    have h2 : 4 * (2 * x + 1) < 8 * y ^ 3 + 4 * y ^ 2 + 3 * y + 3 := by
      by_contra h2
      push Not at h2
      have := Nat.mul_le_mul h2 h2
      nlinarith
    omega
  have key : ∀ y ∈ [2, 3, 4, 5], ∀ x < 300,
      x ^ 2 + x + 1 ≠ y ^ 6 + y ^ 5 + y ^ 4 + y ^ 3 + y ^ 2 + y + 1 := by
    decide +kernel
  have hx : x < 300 := by
    interval_cases y <;> nlinarith
  exact key y (by interval_cases y <;> simp) x hx h

theorem goor37_repunit (x y : ℕ) (hy : 2 ≤ y) : repunit x 3 ≠ repunit y 7 := by
  intro h
  have h' : x ^ 2 + x + 1 = y ^ 6 + y ^ 5 + y ^ 4 + y ^ 3 + y ^ 2 + y + 1 := by
    simp only [repunit, Finset.sum_range_succ, Finset.sum_range_zero] at h
    linarith
  exact goor37 x y hy h'
