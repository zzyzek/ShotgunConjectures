/-
OEIS A110034, Mathlib proof of J. M. Bergot's conjecture |a(n)| = Σ_{k=1..n-1} A061646(k),
for n ≥ 1 (the statement is false at n = 0, where a(0) = 1 and the sum is empty).

Definitions, as in the entries.
* `A110034_H n`: the n × n Hankel matrix (F(i+j-1))_{1 ≤ i,j ≤ n} of Fibonacci numbers
  (0-based: entry (i, j) is F(i+j+1)).
* `A110033 n k`: coefficient of x^k in the characteristic polynomial det(x I - H_n)
  (triangle A110033, row n, k = 0..n).
* `A110034 n` = Σ_{k=0..n} A110033(n, k) (row sums).
* `A061646_g`: A061646 shifted to start at index 0: A061646_g m = A061646(m - 1), with
  a(-1) = a(0) = a(1) = 1 and a(n) = 2 a(n-1) + 2 a(n-2) - a(n-3); `A061646 k` = A061646_g (k+1).

Main theorem `A110034_conjecture`: for n ≥ 1, |A110034 n| = Σ_{k=1..n-1} A061646(k);
`A110034_formula`: for n ≥ 1, A110034 n = -Σ_{k=1..n-1} A061646(k).
`A110034_zero`: A110034 0 = 1 while the sum is 0 (the n = 0 case of the literal statement fails).

Proof. Row sum = charpoly at 1 = det(1 - H). F(i+j+1) = F(i)F(j) + F(i+1)F(j+1) gives H = U Uᵀ with
U the n × 2 matrix of rows (F(i+1), F(i)); det(1 - U Uᵀ) = det(1 - Uᵀ U) (Weinstein–Aronszajn,
`Matrix.det_one_sub_mul_comm`), a 2 × 2 determinant in Σ F(i+1)^2, Σ F(i)^2, Σ F(i)F(i+1).
These sums have closed forms (F(n)F(n+1), F(n-1)F(n), F(n)^2 - [n odd]); A061646(k) = 2F(k)^2 + (-1)^k;
the identity then follows from Cassini's identity.

Not checked in Lean: nothing beyond the reading of the entries' definitions above.
-/
import Mathlib

open Finset Matrix

/-- Hankel matrix (F(i+j-1))_{1 ≤ i,j ≤ n}, 0-based. -/
def A110034_H (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => (Nat.fib (i.val + j.val + 1) : ℤ)

/-- A110033(n, k): coefficient of x^k in the characteristic polynomial of H_n. -/
noncomputable def A110033 (n k : ℕ) : ℤ := (A110034_H n).charpoly.coeff k

/-- A110034(n): row sums of A110033. -/
noncomputable def A110034 (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), A110033 n k

/-- A061646 with offset shifted by one: A061646_g m = A061646(m - 1). -/
def A061646_g : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | k + 3 => 2 * A061646_g (k + 2) + 2 * A061646_g (k + 1) - A061646_g k

/-- A061646(k) for k ≥ 0. -/
def A061646 (k : ℕ) : ℤ := A061646_g (k + 1)

theorem A110034_det (n : ℕ) : A110034 n = det (1 - A110034_H n) := by
  have h := Polynomial.eval_eq_sum_range' (p := (A110034_H n).charpoly) (n := n + 1)
    (by rw [charpoly_natDegree_eq_dim]; simp) 1
  simp only [one_pow, mul_one] at h
  rw [A110034, show (∑ k ∈ range (n + 1), A110033 n k) = (A110034_H n).charpoly.eval 1 from h.symm,
    eval_charpoly, map_one]

/-- The n × 2 matrix with rows (F(i+1), F(i)). -/
def A110034_U (n : ℕ) : Matrix (Fin n) (Fin 2) ℤ :=
  fun i c => if c = 0 then (Nat.fib (i.val + 1) : ℤ) else (Nat.fib i.val : ℤ)

theorem A110034_H_eq (n : ℕ) : A110034_H n = A110034_U n * (A110034_U n)ᵀ := by
  ext i j
  simp only [A110034_H, A110034_U, mul_apply, transpose_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
  rw [Nat.fib_add]
  push_cast
  ring

theorem A110034_det2 (n : ℕ) :
    A110034 n = (1 - ∑ i ∈ range n, (Nat.fib (i + 1) : ℤ) ^ 2) * (1 - ∑ i ∈ range n, (Nat.fib i : ℤ) ^ 2) -
      (∑ i ∈ range n, (Nat.fib i : ℤ) * Nat.fib (i + 1)) ^ 2 := by
  have e00 : ((A110034_U n)ᵀ * A110034_U n) 0 0 = ∑ i ∈ range n, (Nat.fib (i + 1) : ℤ) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [mul_apply, A110034_U, sq]
  have e11 : ((A110034_U n)ᵀ * A110034_U n) 1 1 = ∑ i ∈ range n, (Nat.fib i : ℤ) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [mul_apply, A110034_U, sq]
  have e01 : ((A110034_U n)ᵀ * A110034_U n) 0 1 = ∑ i ∈ range n, (Nat.fib i : ℤ) * Nat.fib (i + 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [mul_apply, A110034_U, mul_comm]
  have e10 : ((A110034_U n)ᵀ * A110034_U n) 1 0 = ∑ i ∈ range n, (Nat.fib i : ℤ) * Nat.fib (i + 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [mul_apply, A110034_U]
  rw [A110034_det, A110034_H_eq, det_one_sub_mul_comm, det_fin_two]
  simp only [Matrix.sub_apply, e00, e11, e01, e10, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  ring

theorem A110034_cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib m * Nat.fib (m + 1) - (Nat.fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.fib_add_two]
    push_cast
    rw [pow_succ]
    linear_combination (-1 : ℤ) * ih

theorem A110034_S11 (n : ℕ) :
    ∑ i ∈ range n, (Nat.fib (i + 1) : ℤ) ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.fib_add_two]
    push_cast
    ring

theorem A110034_S00 (m : ℕ) :
    ∑ i ∈ range (m + 1), (Nat.fib i : ℤ) ^ 2 = Nat.fib m * Nat.fib (m + 1) := by
  rw [sum_range_succ', A110034_S11]
  simp

theorem A110034_S01 (n : ℕ) :
    2 * ∑ i ∈ range n, (Nat.fib i : ℤ) * Nat.fib (i + 1) = 2 * (Nat.fib n : ℤ) ^ 2 - 1 + (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    have hc := A110034_cassini n
    rw [pow_succ]
    linear_combination (-2 : ℤ) * hc

theorem A110034_fib2 (k : ℕ) : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
  rw [Nat.fib_add_two]
  push_cast
  ring

theorem A061646_closed3 (k : ℕ) :
    A061646_g (k + 1) = 2 * (Nat.fib k : ℤ) ^ 2 + (-1) ^ k ∧
      A061646_g (k + 2) = 2 * (Nat.fib (k + 1) : ℤ) ^ 2 + (-1) ^ (k + 1) ∧
        A061646_g (k + 3) = 2 * (Nat.fib (k + 2) : ℤ) ^ 2 + (-1) ^ (k + 2) := by
  induction k with
  | zero => simp [A061646_g, Nat.fib_two]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have e : A061646_g (k + 1 + 3) =
        2 * A061646_g (k + 3) + 2 * A061646_g (k + 2) - A061646_g (k + 1) := rfl
    rw [e, h3, h2, h1, show k + 1 + 2 = k + 3 by ring, show k + 3 = (k + 1) + 2 by ring,
      A110034_fib2 (k + 1), show k + 1 + 1 = k + 2 by ring, A110034_fib2 k]
    ring

theorem A061646_closed (k : ℕ) : A061646_g (k + 1) = 2 * (Nat.fib k : ℤ) ^ 2 + (-1) ^ k :=
  (A061646_closed3 k).1

theorem A110034_formula (n : ℕ) (hn : 1 ≤ n) : A110034 n = -∑ k ∈ Ico 1 n, A061646 k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he : ∀ m : ℕ, 2 * ∑ k ∈ range m, ((-1 : ℤ) ^ (k + 1)) = (-1) ^ m - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, mul_add, ih]; ring
  have hsum : 2 * ∑ k ∈ Ico 1 (m + 1), A061646 k =
      4 * ((Nat.fib m : ℤ) * Nat.fib (m + 1)) + (-1) ^ m - 1 := by
    rw [sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
    have h1 : ∑ k ∈ range m, A061646 (1 + k) =
        ∑ k ∈ range m, (2 * (Nat.fib (k + 1) : ℤ) ^ 2 + (-1) ^ (k + 1)) := by
      refine sum_congr rfl fun k _ => ?_
      rw [A061646, show 1 + k + 1 = (k + 1) + 1 by ring, A061646_closed]
    rw [h1, sum_add_distrib, ← mul_sum, A110034_S11]
    linear_combination he m
  have h01 := A110034_S01 (m + 1)
  have hc := A110034_cassini m
  have hs : ((-1 : ℤ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [pow_succ] at h01
  rw [A110034_det2, A110034_S11, A110034_S00, show m + 1 + 1 = m + 2 by ring, A110034_fib2]
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  set S := ∑ i ∈ range (m + 1), (Nat.fib i : ℤ) * Nat.fib (i + 1)
  set T := ∑ k ∈ Ico 1 (m + 1), A061646 k
  set y := (Nat.fib (m + 1) : ℤ)
  set s := ((-1 : ℤ) ^ m)
  linear_combination (-(2 * S + (2 * y ^ 2 - 1 - s))) * h01 + 2 * hsum + (-4 * y ^ 2) * hc +
    (-1 : ℤ) * hs

theorem A110034_conjecture (n : ℕ) (hn : 1 ≤ n) : |A110034 n| = ∑ k ∈ Ico 1 n, A061646 k := by
  have hpos : 0 ≤ ∑ k ∈ Ico 1 n, A061646 k := by
    refine sum_nonneg fun k hk => ?_
    rw [mem_Ico] at hk
    rw [A061646, A061646_closed]
    have hf : 1 ≤ Nat.fib k := Nat.fib_pos.mpr (by omega)
    have hf' : (1 : ℤ) ≤ Nat.fib k := by exact_mod_cast hf
    rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> nlinarith
  rw [A110034_formula n hn, abs_neg, abs_of_nonneg hpos]

theorem A110034_zero : A110034 0 = 1 ∧ ∑ k ∈ Ico 1 0, A061646 k = 0 := by
  refine ⟨?_, by simp⟩
  rw [A110034_det]
  simp

theorem A110034_data :
    (List.range 14).map (fun n => -∑ k ∈ Ico 1 n, A061646 k) =
      [0, 0, -1, -4, -11, -30, -79, -208, -545, -1428, -3739, -9790, -25631, -67104] ∧
    (List.range 15).map A061646_g = [1, 1, 1, 3, 7, 19, 49, 129, 337, 883, 2311, 6051, 15841, 41473, 108577] := by
  decide
