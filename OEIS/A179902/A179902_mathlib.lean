import Mathlib

/-
OEIS A179902 (offset 1): row sums of the triangle A179901.  A179901: "Triangle
read by rows, antidiagonals of an array generated from (1, r, r, r, ...)
convolved with (1, 0, r, r, r, ...)"; array row r (r >= 1) is the convolution,
row n of the triangle is (A(n,1), A(n-1,2), ..., A(1,n)) (the entry's example
and A. Howroyd's PARI program).
Conjecture (entry): the parities are 1, 0, 1, 1, 1, 0, 1, 1, ..., i.e. a(n) is
even exactly when n = 2 (mod 4).

Definitions.  `u r i`, `v r j`: the coefficients of (1, r, r, ...) and
(1, 0, r, r, ...); `arr r m` = coefficient m of their product (array row r,
column m + 1); `T n k = arr (n + 1 - k) (k - 1)`; `A179902 n = Σ_{k=1..n} T n k`.

Main theorems.
* `A179902_parity`: for n ≥ 1, A179902 n % 2 = if n % 4 = 2 then 0 else 1.
* `A179902_closed`: 12 a(n) = n^4 - 8n^3 + 35n^2 - 52n + 36 for n ≥ 1
  (A. Howroyd's formula in the entry).

Route.  `arr_two`: coefficient m + 2 is 2r + r^2 m.  Summing the antidiagonal
with the power sums `s1`, `s2`, `s3` gives `A179902_closed`.  Then
3 (a(n+4) - a(n)) = 2 (2n^3 + 19n + 12), so a(n+4) - a(n) is even, and
a(1..4) = 1, 2, 5, 11.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py recomputes them from the same definition).
-/

namespace OEIS

def u (r i : ℕ) : ℕ := if i = 0 then 1 else r
def v (r j : ℕ) : ℕ := if j = 0 then 1 else if j = 1 then 0 else r

/-- Coefficient m of (1, r, r, ...) * (1, 0, r, r, ...): array row r, column m + 1. -/
def arr (r m : ℕ) : ℕ := ∑ i ∈ Finset.range (m + 1), u r i * v r (m - i)

/-- A179901 as a triangle, 1 ≤ k ≤ n: the n-th antidiagonal read from row n. -/
def T (n k : ℕ) : ℕ := arr (n + 1 - k) (k - 1)

/-- Row sums of A179901. -/
def A179902 (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, T n k

theorem arr_zero (r : ℕ) : arr r 0 = 1 := by simp [arr, u, v]

theorem arr_one (r : ℕ) : arr r 1 = r := by
  simp [arr, u, v, Finset.sum_range_succ]

theorem arr_two (r m : ℕ) : arr r (m + 2) = 2 * r + r ^ 2 * m := by
  rw [arr, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ']
  have h : ∀ i ∈ Finset.range m, u r (i + 1) * v r (m + 2 - (i + 1)) = r * r := by
    intro i hi
    simp at hi
    simp only [u, v, show i + 1 ≠ 0 by omega, show m + 2 - (i + 1) ≠ 0 by omega,
      show m + 2 - (i + 1) ≠ 1 by omega, ite_false]
  rw [Finset.sum_congr rfl h]
  simp [u, v]
  ring

theorem A179902_range (n : ℕ) :
    A179902 n = ∑ j ∈ Finset.range n, arr (n - j) j := by
  have e : Finset.Icc 1 n = Finset.Ico (0 + 1) (n + 1) := by ext; simp
  rw [A179902, e, ← Finset.sum_Ico_add', Finset.range_eq_Ico]
  apply Finset.sum_congr rfl
  intro j _
  simp only [T]
  congr 1; omega

theorem s1 (M : ℕ) : 2 * ∑ i ∈ Finset.range M, (i : ℤ) = M * (M - 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

theorem s2 (M : ℕ) : 6 * ∑ i ∈ Finset.range M, (i : ℤ) ^ 2 = (M - 1) * M * (2 * M - 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

theorem s3 (M : ℕ) : 4 * ∑ i ∈ Finset.range M, (i : ℤ) ^ 3 = M ^ 2 * (M - 1) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

theorem G_eq (M : ℕ) :
    ((∑ i ∈ Finset.range M, arr (M - i) (i + 2) : ℕ) : ℤ)
      = 2 * M * M - 2 * ∑ i ∈ Finset.range M, (i : ℤ)
        + M ^ 2 * ∑ i ∈ Finset.range M, (i : ℤ)
        - 2 * M * ∑ i ∈ Finset.range M, (i : ℤ) ^ 2
        + ∑ i ∈ Finset.range M, (i : ℤ) ^ 3 := by
  push_cast
  have h : ∀ i ∈ Finset.range M, ((arr (M - i) (i + 2) : ℕ) : ℤ)
      = 2 * M - 2 * i + M ^ 2 * i - 2 * M * i ^ 2 + i ^ 3 := by
    intro i hi
    simp at hi
    rw [arr_two]
    push_cast [Nat.cast_sub hi.le]
    ring
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- A. Howroyd's closed form. -/
theorem A179902_closed (n : ℕ) (hn : 1 ≤ n) :
    12 * (A179902 n : ℤ) = n ^ 4 - 8 * n ^ 3 + 35 * n ^ 2 - 52 * n + 36 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [A179902_range]; simp [arr_zero]
  · obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
    rw [A179902_range, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [show M + 2 - (0 + 1) = M + 1 by omega, show M + 2 - 0 = M + 2 by omega,
      show (0 + 1 : ℕ) = 1 by rfl, show ∀ i, i + 1 + 1 = i + 2 from fun i => rfl, arr_one,
      arr_zero, Nat.add_sub_add_right]
    push_cast
    have hG := G_eq M
    push_cast at hG
    rw [hG]
    linear_combination (6 * (M : ℤ) ^ 2 - 12) * s1 M - 4 * (M : ℤ) * s2 M + 3 * s3 M

theorem step4 (n : ℕ) (hn : 1 ≤ n) : (A179902 (n + 4) % 2) = A179902 n % 2 := by
  have h1 := A179902_closed (n + 4) (by omega)
  have h0 := A179902_closed n hn
  have key4 : 4 * (3 * ((A179902 (n + 4) : ℤ) - A179902 n))
      = 4 * (2 * (2 * n ^ 3 + 19 * n + 12)) := by
    push_cast at h1
    linear_combination h1 - h0
  have key : 3 * ((A179902 (n + 4) : ℤ) - A179902 n) = 2 * (2 * n ^ 3 + 19 * n + 12) := by
    linarith
  generalize (2 * (n : ℤ) ^ 3 + 19 * n + 12) = X at key
  omega

/-- The conjectured parity pattern 1, 0, 1, 1, 1, 0, 1, 1, ... holds. -/
theorem A179902_parity (n : ℕ) (hn : 1 ≤ n) :
    A179902 n % 2 = if n % 4 = 2 then 0 else 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [step4 m (by omega), ih m (by omega) (by omega)]
      simp only [show (m + 4) % 4 = m % 4 by omega]
