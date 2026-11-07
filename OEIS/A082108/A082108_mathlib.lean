/-
OEIS A082108 (Mathlib): a(n) = 4n^2 + 6n + 1 (offset 0).

The scan's conjecture reads "a(n-1) is the largest integer such that Sum[a(k)/(2k)!, k=1..n] is less than 1".
Taken literally it fails at once (a(1)/2! = 11/2 > 1); the summand index is a slip for a(k-1), as in
Robert Israel's formula in the entry: Sum_{k=1..n} a(k-1)/(2k)! = 1 - 1/(2n)!.
Checked here (index shifted by one, k -> k+1, n -> n+1):
* `A082108_partial_sum`: Sum_{k<n} a(k)/(2k+2)! = 1 - 1/(2n)!  (Israel's formula).
* `A082108_isGreatest`: a(n) is the largest integer x with Sum_{k<n} a(k)/(2k+2)! + x/(2n+2)! < 1.
* `A082108_literal_false`: the literal reading fails for n = 1.
-/
import Mathlib

/-- A082108(n) = 4n^2 + 6n + 1 (the OEIS definition). -/
def A082108 (n : ℕ) : ℤ := 4 * n ^ 2 + 6 * n + 1

theorem A082108_fact (n : ℕ) :
    ((2 * n + 2).factorial : ℚ) = (2 * n + 2) * (2 * n + 1) * ((2 * n).factorial : ℚ) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast; ring

theorem A082108_partial_sum (n : ℕ) :
    ∑ k ∈ Finset.range n, (A082108 k : ℚ) / ((2 * k + 2).factorial : ℚ) =
      1 - 1 / ((2 * n).factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (n + 1) = 2 * n + 2 by ring, A082108_fact]
    have hf : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
    unfold A082108; push_cast
    field_simp
    ring

/-- Main theorem: a(n) is the largest integer x with Sum_{k<n} a(k)/(2k+2)! + x/(2n+2)! < 1. -/
theorem A082108_isGreatest (n : ℕ) :
    IsGreatest {x : ℤ | ∑ k ∈ Finset.range n, (A082108 k : ℚ) / ((2 * k + 2).factorial : ℚ) +
      (x : ℚ) / ((2 * n + 2).factorial : ℚ) < 1} (A082108 n) := by
  have key : ∀ x : ℤ, (∑ k ∈ Finset.range n, (A082108 k : ℚ) / ((2 * k + 2).factorial : ℚ) +
      (x : ℚ) / ((2 * n + 2).factorial : ℚ) < 1 ↔ x ≤ A082108 n) := by
    intro x
    rw [A082108_partial_sum, A082108_fact]
    have hf : (0 : ℚ) < ((2 * n).factorial : ℚ) := by positivity
    have hF : (0 : ℚ) < (2 * n + 2) * (2 * n + 1) * ((2 * n).factorial : ℚ) := by positivity
    have e : (1 : ℚ) - 1 / ((2 * n).factorial : ℚ) + x / ((2 * n + 2) * (2 * n + 1) * ((2 * n).factorial : ℚ)) =
        1 + (x - (2 * n + 2) * (2 * n + 1)) / ((2 * n + 2) * (2 * n + 1) * ((2 * n).factorial : ℚ)) := by
      field_simp; ring
    rw [e, add_lt_iff_neg_left, div_lt_iff₀ hF, zero_mul, sub_neg]
    unfold A082108
    constructor
    · intro h
      have h' : x < (2 * (n : ℤ) + 2) * (2 * n + 1) := by exact_mod_cast h
      nlinarith
    · intro h
      have h' : x < (2 * (n : ℤ) + 2) * (2 * n + 1) := by nlinarith
      exact_mod_cast h'
  exact ⟨(key _).mpr le_rfl, fun x hx => (key x).mp hx⟩

/-- The literal reading (summand a(k)) fails: for n = 1 the sum a(1)/2! = 11/2 is not below 1. -/
theorem A082108_literal_false :
    ¬ (∑ k ∈ Finset.Icc 1 1, (A082108 k : ℚ) / ((2 * k).factorial : ℚ) < 1) := by
  simp [A082108, Nat.factorial]
  norm_num
