import Mathlib

/-!
# OEIS A212346: a(n) = (n+3)(n^2-4)/6 for n >= 3

`N k n` is the number of 132-avoiding permutations of length `n` in which every entry has fewer than
`k` larger entries to its left, given by the first-entry decomposition (the largest entry splits a
132-avoider into a left block of size `i` above a right block of size `n-1-i`; every right-block entry
gains `i+1` larger entries on its left):
`N k 0 = 1`, `N 0 (n+1) = 0`, `N (k+1) (n+1) = sum_{i<=n} N (k+1) i * N (k-i) (n-i)`.
A212346 is `N 4`.

Checked here: `A212346_formula` : `6 * N 4 n = (n+3)(n^2-4)` for `n >= 3`, derived from the recursion.
Not checked here: that the recursion counts the permutations (the decomposition above; brute force
in certificate/brute.py for n <= 10 and the published generating function of Kitaev, Remmel,
Tiefenbruck, Theorem for Q^{(0,k,0,0)}_{132}).
-/

namespace A212346

open Finset

def N : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, n + 1 => ∑ i : Fin (n + 1), N (k + 1) i * N (k - i) (n - i)
termination_by _ n => n
decreasing_by all_goals (have := i.isLt; omega)

theorem N_zero_succ (n : ℕ) : N 0 (n + 1) = 0 := by rw [N]

theorem N_succ_succ (k n : ℕ) :
    N (k + 1) (n + 1) = ∑ i ∈ range (n + 1), N (k + 1) i * N (k - i) (n - i) := by
  rw [N, Finset.sum_range (fun i => N (k + 1) i * N (k - i) (n - i))]

theorem step (k n : ℕ) (h : k ≤ n) :
    N (k + 1) (n + 1) = N (k + 1) n + ∑ i ∈ range k, N (k + 1) i * N (k - i) (n - i) := by
  rw [N_succ_succ, Finset.sum_range_succ, Nat.sub_self, N, Nat.mul_one, add_comm,
    Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) h]
  have hz : ∑ i ∈ Ico k n, N (k + 1) i * N (k - i) (n - i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h1 : k - i = 0 := by omega
    obtain ⟨m, hm⟩ : ∃ m, n - i = m + 1 := ⟨n - i - 1, by omega⟩
    rw [h1, hm, N_zero_succ, Nat.mul_zero]
  rw [hz, Finset.range_eq_Ico]
  rfl

theorem N_zero (k : ℕ) : N k 0 = 1 := by rw [N]

theorem N1 (n : ℕ) : N 1 n = 1 := by
  induction n with
  | zero => exact N_zero 1
  | succ n ih =>
    rw [step 0 n (Nat.zero_le n), Finset.sum_range_zero, ih]
    rfl

theorem N2 (n : ℕ) (h : 1 ≤ n) : N 2 n = n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [N_succ_succ, Finset.sum_range_one, N_zero, N_zero]
    · rw [step 1 n hn, Finset.sum_range_one, ih hn, N_zero, N1]

theorem N31 : N 3 1 = 1 := by rw [N_succ_succ, Finset.sum_range_one, N_zero, N_zero]

theorem N41 : N 4 1 = 1 := by rw [N_succ_succ, Finset.sum_range_one, N_zero, N_zero]

theorem N42 : N 4 2 = 2 := by
  rw [N_succ_succ, Finset.sum_range_succ, Finset.sum_range_one, N_zero, N_zero, N41]
  simp only [Nat.reduceSub, Nat.one_mul]
  rw [N31]

/-- Recurrences for `n ≥ 2` and `n ≥ 3`, from `step`. -/
theorem N3_rec (n : ℕ) (hn : 2 ≤ n) : N 3 (n + 1) = N 3 n + n + 1 := by
  have e : N 3 (n + 1) = N 3 n + ∑ i ∈ range 2, N 3 i * N (2 - i) (n - i) := step 2 n hn
  rw [e, Finset.sum_range_succ, Finset.sum_range_one, N_zero, N31]
  simp only [Nat.reduceSub, Nat.sub_zero, Nat.one_mul, N1]
  rw [N2 n (by omega)]
  omega

theorem N3 (n : ℕ) (h : 2 ≤ n) : 2 * N 3 n + 2 = n * n + n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · obtain rfl : n = 1 := by omega
      rw [N_succ_succ, Finset.sum_range_succ, Finset.sum_range_one, N_zero, N_zero, N31]
      simp only [Nat.reduceSub, Nat.one_mul]
      rw [N2 1 le_rfl]
    · rw [N3_rec n hn]
      have := ih hn
      nlinarith

theorem N4_rec (n : ℕ) (hn : 3 ≤ n) : N 4 (n + 1) = N 4 n + N 3 n + (n - 1) + 2 := by
  have e : N 4 (n + 1) = N 4 n + ∑ i ∈ range 3, N 4 i * N (3 - i) (n - i) := step 3 n hn
  rw [e, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, N_zero,
    N41, N42]
  simp only [Nat.reduceSub, Nat.sub_zero, Nat.one_mul, N1]
  rw [N2 (n - 1) (by omega)]
  omega

theorem N4_three : N 4 3 = 5 := by
  rw [N_succ_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, N_zero,
    N41, N42]
  simp only [Nat.reduceSub, Nat.sub_self, Nat.one_mul, N_zero]
  have := N3 2 le_rfl
  rw [N2 1 le_rfl]
  omega

theorem N4_poly (n : ℕ) (h : 3 ≤ n) : 6 * N 4 n + 4 * (n + 3) = (n + 3) * (n * n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · obtain rfl : n = 2 := by omega
      rw [N4_three]
    · rw [N4_rec n hn]
      have h3 := N3 n (by omega)
      have ih' := ih hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at *
      nlinarith

/-- A212346: `a(n) = (n+3)(n^2-4)/6` for `n ≥ 3`, with `a = N 4`. -/
theorem A212346_formula (n : ℕ) (h : 3 ≤ n) : 6 * N 4 n = (n + 3) * (n * n - 4) := by
  have := N4_poly n h
  rw [Nat.mul_sub]
  generalize (n + 3) * (n * n) = X at *
  omega

