import Mathlib

/-
OEIS A103910: triangle T read by rows, the inverse of the Fibonomial
triangle A010048.  Conjecture (entry): all rows except the first add to zero.

Definitions.  `fibonomial n k` = prod_{i<k} F(n-i) / prod_{i<k} F(i+1)
(A010048, natural-number division; exact for k <= n, not needed here
beyond k = 0 and k = n).  `Fib N` is the (N+1) x (N+1) lower triangular
truncation over Q.  Since the triangle is lower unitriangular, the first
N+1 rows of its inverse are the rows of `(Fib N)⁻¹`.

Main theorems.
* `rowsum_of_left_inv`: any T with T * Fib N = 1 has row sums 1, 0, 0, ...
* `A103910_rowsum`: the same for T = (Fib N)⁻¹ (det = 1, `det_Fib`).

Route.  Column 0 of the Fibonomial triangle is all ones, so
Fib N *ᵥ e₀ = 1 and T *ᵥ 1 = (T * Fib N) *ᵥ e₀ = e₀.
Not checked: that `fibonomial` reproduces A010048 for 0 < k < n (unused).
-/

open Matrix

namespace A103910

/-- A010048 (Fibonomial coefficient) for k ≤ n. -/
def fibonomial (n k : ℕ) : ℕ :=
  (∏ i ∈ Finset.range k, Nat.fib (n - i)) / ∏ i ∈ Finset.range k, Nat.fib (i + 1)

/-- The Fibonomial triangle, rows and columns 0..N. -/
def Fib (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  fun i j => if j ≤ i then (fibonomial i j : ℚ) else 0

lemma fibonomial_zero (n : ℕ) : fibonomial n 0 = 1 := by simp [fibonomial]

lemma fibonomial_self (n : ℕ) : fibonomial n n = 1 := by
  unfold fibonomial
  have h : ∏ i ∈ Finset.range n, Nat.fib (n - i) = ∏ i ∈ Finset.range n, Nat.fib (i + 1) := by
    rw [← Finset.prod_range_reflect (fun i => Nat.fib (i + 1)) n]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    congr 1
    omega
  rw [h]
  exact Nat.div_self (Finset.prod_pos (fun i _ => Nat.fib_pos.mpr (by omega)))

lemma Fib_mulVec_single (N : ℕ) : Fib N *ᵥ Pi.single 0 1 = fun _ => 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  simp [Fib, fibonomial_zero]

theorem rowsum_of_left_inv (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ)
    (hT : T * Fib N = 1) (i : Fin (N + 1)) :
    ∑ j, T i j = if i = 0 then 1 else 0 := by
  have h : T *ᵥ (fun _ => (1 : ℚ)) = Pi.single 0 1 := by
    rw [← Fib_mulVec_single, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  have hi := congrFun h i
  simp only [Matrix.mulVec, dotProduct, mul_one] at hi
  rw [hi]
  by_cases h0 : i = 0
  · subst h0; simp
  · simp [h0]

lemma det_Fib (N : ℕ) : (Fib N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [Fib, fibonomial_self]
  · intro i j hij
    have h : i < j := hij
    simp [Fib, not_le.mpr h]

theorem A103910_rowsum (N : ℕ) (i : Fin (N + 1)) :
    ∑ j, (Fib N)⁻¹ i j = if i = 0 then 1 else 0 := by
  apply rowsum_of_left_inv
  apply Matrix.nonsing_inv_mul
  rw [det_Fib]
  exact isUnit_one
