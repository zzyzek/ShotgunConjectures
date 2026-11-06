/-
OEIS A195673: triangle T(n,k) read by rows, T(0,0) = -2, T(1,0) = 3,
T(1,1) = 0 and T(n,k) = T(n-1,k) - T(n-2,k-2) otherwise.
Conjecture (Paul Curtz, entry text): with other initial constants
T(0,0) = p and T(1,0) = q, the row polynomials
p(n,x,p,q) = sum_{k=0..n} T(n,k) x^(n-k) satisfy
p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x), the Chebyshev S-polynomials of A053119.

Definitions.
* `T p q n k` (n : ℕ, k : ℤ): T p q 0 k = [k = 0] p, T p q 1 k = [k = 0] q,
  T p q (n+2) k = T p q (n+1) k - T p q n (k-2). Entries outside 0 ≤ k ≤ n
  are 0 (`T_neg`, `T_big`), so this is the entry's triangle with the
  "otherwise" recurrence applied for every n ≥ 2.
* `a = T (-2) 3` (the sequence A195673).
* `rowPoly p q n = Σ_{k=0..n} C (T p q n k) * X^(n-k)`.
* S(n,x) is Mathlib's `Polynomial.Chebyshev.S ℤ n` (S 0 = 1, S 1 = X,
  S (n+2) = X S (n+1) - S n), the row polynomials of A053119.

Main theorems.
* `A195673_conjecture`: for all p q : ℤ and n : ℕ,
  rowPoly (p+1) (q+1) n - rowPoly p q n = Chebyshev.S ℤ n.
* `A195673_coeff`: the same coefficientwise, for k ≤ n:
  T (p+1) (q+1) n k - T p q n k = coeff (S ℤ n) (n-k).
* `A195673_data`: rows 0..11 of `a` flattened begin with the
  71 data terms of the entry.

Not checked in this file: nothing beyond the reading above.
-/
import Mathlib

open Polynomial Finset

namespace A195673

def T (p q : ℤ) : ℕ → ℤ → ℤ
  | 0, k => if k = 0 then p else 0
  | 1, k => if k = 0 then q else 0
  | n + 2, k => T p q (n + 1) k - T p q n (k - 2)

def a : ℕ → ℤ → ℤ := T (-2) 3

theorem A195673_data :
    ((List.range 12).flatMap fun n =>
        (List.range (n + 1)).map fun k => a n k).take 71 =
      [-2,3,0,3,0,2,3,0,-1,0,3,0,-4,0,-2,3,0,-7,0,-1,0,3,0,-10,0,3,0,2,3,0,
       -13,0,10,0,3,0,3,0,-16,0,20,0,0,0,-2,3,0,-19,0,33,0,-10,0,-5,0,3,0,
       -22,0,49,0,-30,0,-5,0,2,3,0,-25,0,68] := by
  decide

theorem T_neg (p q : ℤ) : ∀ (n : ℕ) (k : ℤ), k < 0 → T p q n k = 0
  | 0, k, h => by simp [T, show k ≠ 0 by omega]
  | 1, k, h => by simp [T, show k ≠ 0 by omega]
  | n + 2, k, h => by
    rw [T, T_neg p q (n + 1) k h, T_neg p q n (k - 2) (by omega)]; simp

theorem T_big (p q : ℤ) : ∀ (n : ℕ) (k : ℤ), (n : ℤ) < k → T p q n k = 0
  | 0, k, h => by simp [T, show k ≠ 0 by omega]
  | 1, k, h => by simp [T, show k ≠ 0 by omega]
  | n + 2, k, h => by
    rw [T, T_big p q (n + 1) k (by push_cast at h ⊢; omega),
      T_big p q n (k - 2) (by push_cast at h; omega)]; simp

/-- The triangle is linear in the initial constants. -/
theorem T_lin (p q : ℤ) : ∀ (n : ℕ) (k : ℤ),
    T (p + 1) (q + 1) n k = T p q n k + T 1 1 n k
  | 0, k => by by_cases h : k = 0 <;> simp [T, h]
  | 1, k => by by_cases h : k = 0 <;> simp [T, h]
  | n + 2, k => by
    rw [T, T, T, T_lin p q (n + 1) k, T_lin p q n (k - 2)]; ring

noncomputable def rowPoly (p q : ℤ) (n : ℕ) : ℤ[X] :=
  ∑ k ∈ range (n + 1), C (T p q n k) * X ^ (n - k)

theorem rowPoly_rec (p q : ℤ) (n : ℕ) :
    rowPoly p q (n + 2) = X * rowPoly p q (n + 1) - rowPoly p q n := by
  have h1 : rowPoly p q (n + 2) =
      ∑ k ∈ range (n + 3), C (T p q (n + 1) k) * X ^ (n + 2 - k) -
      ∑ k ∈ range (n + 3), C (T p q n ((k : ℤ) - 2)) * X ^ (n + 2 - k) := by
    rw [rowPoly, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [T, C_sub, sub_mul]
  have h2 : ∑ k ∈ range (n + 3), C (T p q (n + 1) k) * X ^ (n + 2 - k) =
      X * rowPoly p q (n + 1) := by
    rw [sum_range_succ, T_big p q (n + 1) ((n + 2 : ℕ) : ℤ) (by push_cast; omega),
      C_0, zero_mul, add_zero, rowPoly, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k < n + 2 := mem_range.mp hk
    rw [show n + 2 - k = (n + 1 - k) + 1 by omega, pow_succ]; ring
  have h3 : ∑ k ∈ range (n + 3), C (T p q n ((k : ℤ) - 2)) * X ^ (n + 2 - k) =
      rowPoly p q n := by
    rw [sum_range_succ', sum_range_succ', T_neg p q n _ (by norm_num),
      T_neg p q n _ (by norm_num), C_0, zero_mul, zero_mul, add_zero, add_zero,
      rowPoly]
    refine sum_congr rfl fun k _ => ?_
    rw [show ((k + 1 + 1 : ℕ) : ℤ) - 2 = (k : ℤ) by push_cast; ring,
      show n + 2 - (k + 1 + 1) = n - k by omega]
  rw [h1, h2, h3]

theorem rowPoly_one_one : ∀ n : ℕ, rowPoly 1 1 n = Chebyshev.S ℤ n
  | 0 => by simp [rowPoly, T]
  | 1 => by simp [rowPoly, T]
  | n + 2 => by
    rw [rowPoly_rec, rowPoly_one_one (n + 1), rowPoly_one_one n,
      show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring,
      show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring,
      Chebyshev.S_add_two]

theorem rowPoly_lin (p q : ℤ) (n : ℕ) :
    rowPoly (p + 1) (q + 1) n = rowPoly p q n + rowPoly 1 1 n := by
  rw [rowPoly, rowPoly, rowPoly, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [T_lin, C_add, add_mul]

theorem A195673_conjecture (p q : ℤ) (n : ℕ) :
    rowPoly (p + 1) (q + 1) n - rowPoly p q n = Chebyshev.S ℤ n := by
  rw [rowPoly_lin, ← rowPoly_one_one]; ring

theorem rowPoly_coeff (p q : ℤ) (n k : ℕ) (hk : k ≤ n) :
    (rowPoly p q n).coeff (n - k) = T p q n k := by
  rw [rowPoly, finsetSum_coeff, sum_eq_single k]
  · rw [coeff_C_mul_X_pow, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
  · intro j hj hjk
    have := mem_range.mp hj
    rw [coeff_C_mul_X_pow]
    exact ite_eq_right_iff.mpr (fun h => absurd (by omega) hjk)
  · intro h; exact absurd (mem_range.mpr (by omega)) h

theorem A195673_coeff (p q : ℤ) (n k : ℕ) (hk : k ≤ n) :
    T (p + 1) (q + 1) n k - T p q n k = (Chebyshev.S ℤ n).coeff (n - k) := by
  rw [← A195673_conjecture p q n, coeff_sub, rowPoly_coeff _ _ n k hk,
    rowPoly_coeff _ _ n k hk]

