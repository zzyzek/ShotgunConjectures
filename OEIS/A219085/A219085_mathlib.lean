import Mathlib

/-
OEIS A219085: a(n) = floor((n + 1/2)^3), the jump points of f(x) = x^(1/3).
Conjecture (C. Kimberling, 2012): for f(x) = x^(1/d), d ≥ 1, the solutions of
{k^(1/d)} < 1/2 < {(k+1)^(1/d)} form a linearly recurrent sequence.  The entry
records that D. Moews proved it.

Checked here, for the entry's own sequence (d = 3):
* `A219085_rec`: a(n+7) = 3a(n+6) - 3a(n+5) + a(n+4) + a(n+3) - 3a(n+2)
  + 3a(n+1) - a(n) for every n ≥ 0 (the entry's recurrence), with
  a(n) = ⌊(n + 1/2)^3⌋ over ℚ.
* `A219085_quasi`: a(4k+j) = (8k+2j+1)^3 div 8, a polynomial in k for each j.
* `A219085_data`: the first 12 listed terms.

Not checked: that the jump points of x^(1/d) are ⌊(n+1/2)^d⌋ (k is a jump point
iff k < (n+1/2)^d < k+1 for some n; (n+1/2)^d is never an integer), and
general d (README: ⌊(2n+1)^d / 2^d⌋ is a quasi-polynomial of period 2^d).
-/

noncomputable def A219085_a (n : ℕ) : ℤ := ⌊((n : ℚ) + 1 / 2) ^ 3⌋

theorem A219085_floor (z : ℤ) (r : ℚ) (h0 : 0 ≤ r) (h1 : r < 1) : ⌊(z : ℚ) + r⌋ = z := by
  rw [Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩, add_zero]

theorem A219085_quasi (k : ℕ) :
    A219085_a (4 * k) = 64 * k ^ 3 + 24 * k ^ 2 + 3 * k ∧
    A219085_a (4 * k + 1) = 64 * k ^ 3 + 72 * k ^ 2 + 27 * k + 3 ∧
    A219085_a (4 * k + 2) = 64 * k ^ 3 + 120 * k ^ 2 + 75 * k + 15 ∧
    A219085_a (4 * k + 3) = 64 * k ^ 3 + 168 * k ^ 2 + 147 * k + 42 := by
  unfold A219085_a
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (((4 * k : ℕ) : ℚ) + 1 / 2) ^ 3 =
        ((64 * k ^ 3 + 24 * k ^ 2 + 3 * k : ℤ) : ℚ) + 1 / 8 by push_cast; ring]
    exact A219085_floor _ _ (by norm_num) (by norm_num)
  · rw [show (((4 * k + 1 : ℕ) : ℚ) + 1 / 2) ^ 3 =
        ((64 * k ^ 3 + 72 * k ^ 2 + 27 * k + 3 : ℤ) : ℚ) + 3 / 8 by push_cast; ring]
    exact A219085_floor _ _ (by norm_num) (by norm_num)
  · rw [show (((4 * k + 2 : ℕ) : ℚ) + 1 / 2) ^ 3 =
        ((64 * k ^ 3 + 120 * k ^ 2 + 75 * k + 15 : ℤ) : ℚ) + 5 / 8 by push_cast; ring]
    exact A219085_floor _ _ (by norm_num) (by norm_num)
  · rw [show (((4 * k + 3 : ℕ) : ℚ) + 1 / 2) ^ 3 =
        ((64 * k ^ 3 + 168 * k ^ 2 + 147 * k + 42 : ℤ) : ℚ) + 7 / 8 by push_cast; ring]
    exact A219085_floor _ _ (by norm_num) (by norm_num)

theorem A219085_rec (n : ℕ) :
    A219085_a (n + 7) = 3 * A219085_a (n + 6) - 3 * A219085_a (n + 5) + A219085_a (n + 4) +
      A219085_a (n + 3) - 3 * A219085_a (n + 2) + 3 * A219085_a (n + 1) - A219085_a n := by
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 4 ∧ n = 4 * k + j :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have q0 := fun k => (A219085_quasi k).1
  have q1 := fun k => (A219085_quasi k).2.1
  have q2 := fun k => (A219085_quasi k).2.2.1
  have q3 := fun k => (A219085_quasi k).2.2.2
  interval_cases j
  · rw [show 4 * k + 0 + 7 = 4 * (k + 1) + 3 by ring, show 4 * k + 0 + 6 = 4 * (k + 1) + 2 by ring,
      show 4 * k + 0 + 5 = 4 * (k + 1) + 1 by ring, show 4 * k + 0 + 4 = 4 * (k + 1) by ring,
      show 4 * k + 0 + 3 = 4 * k + 3 by ring, show 4 * k + 0 + 2 = 4 * k + 2 by ring,
      show 4 * k + 0 + 1 = 4 * k + 1 by ring, show 4 * k + 0 = 4 * k by ring]
    simp only [q0, q1, q2, q3]; push_cast; ring
  · rw [show 4 * k + 1 + 7 = 4 * (k + 2) by ring, show 4 * k + 1 + 6 = 4 * (k + 1) + 3 by ring,
      show 4 * k + 1 + 5 = 4 * (k + 1) + 2 by ring, show 4 * k + 1 + 4 = 4 * (k + 1) + 1 by ring,
      show 4 * k + 1 + 3 = 4 * (k + 1) by ring, show 4 * k + 1 + 2 = 4 * k + 3 by ring,
      show 4 * k + 1 + 1 = 4 * k + 2 by ring]
    simp only [q0, q1, q2, q3]; push_cast; ring
  · rw [show 4 * k + 2 + 7 = 4 * (k + 2) + 1 by ring, show 4 * k + 2 + 6 = 4 * (k + 2) by ring,
      show 4 * k + 2 + 5 = 4 * (k + 1) + 3 by ring, show 4 * k + 2 + 4 = 4 * (k + 1) + 2 by ring,
      show 4 * k + 2 + 3 = 4 * (k + 1) + 1 by ring, show 4 * k + 2 + 2 = 4 * (k + 1) by ring,
      show 4 * k + 2 + 1 = 4 * k + 3 by ring]
    simp only [q0, q1, q2, q3]; push_cast; ring
  · rw [show 4 * k + 3 + 7 = 4 * (k + 2) + 2 by ring, show 4 * k + 3 + 6 = 4 * (k + 2) + 1 by ring,
      show 4 * k + 3 + 5 = 4 * (k + 2) by ring, show 4 * k + 3 + 4 = 4 * (k + 1) + 3 by ring,
      show 4 * k + 3 + 3 = 4 * (k + 1) + 2 by ring, show 4 * k + 3 + 2 = 4 * (k + 1) + 1 by ring,
      show 4 * k + 3 + 1 = 4 * (k + 1) by ring]
    simp only [q0, q1, q2, q3]; push_cast; ring

theorem A219085_data :
    (List.range 12).map A219085_a = [0, 3, 15, 42, 91, 166, 274, 421, 614, 857, 1157, 1520] := by
  have q0 := fun k => (A219085_quasi k).1
  have q1 := fun k => (A219085_quasi k).2.1
  have q2 := fun k => (A219085_quasi k).2.2.1
  have q3 := fun k => (A219085_quasi k).2.2.2
  have e : (List.range 12) = [4 * 0, 4 * 0 + 1, 4 * 0 + 2, 4 * 0 + 3, 4 * 1, 4 * 1 + 1, 4 * 1 + 2,
      4 * 1 + 3, 4 * 2, 4 * 2 + 1, 4 * 2 + 2, 4 * 2 + 3] := by decide
  rw [e]
  simp only [List.map_cons, List.map_nil, q0, q1, q2, q3]
  norm_num
