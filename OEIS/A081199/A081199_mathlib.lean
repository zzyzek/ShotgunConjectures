/-
OEIS A081199, Mathlib proof.

A081199(n) = Σ_j C(n, j)·5^(n-j)·[j odd] (5-th binomial transform of
0, 1, 0, 1, ...). Conjecture (R. H. Hardin, 2010): a(n) is the number of
collinear 4-tuples of points in the 4 × 4 × ... × 4 n-dimensional cubic grid.

Reading: a collinear 4-tuple is a 4-element set of grid points lying on one
line (Mathlib `Collinear ℝ` of the set). The grid is {0, ..., 3}^n
(`Fin n → Fin 4`, embedded in ℝ^n); translating to {1, ..., 4}^n does not
change collinearity.

Main theorem `A081199_main`: for every n, the number of 4-element subsets S of
the grid with `Collinear ℝ` (image of S in ℝ^n) equals A081199(n), and equals
(6^n - 4^n)/2. This is the README result.

Proof (library `OpenProblemsLib.D_CombLine`, general k ≥ 2): a collinear
k-set of {0..k-1}^n is a combinatorial line (each coordinate constant,
increasing or decreasing along it, not all constant), and each line has
exactly two such descriptions. Nothing is outside Lean.
-/
import Mathlib
import OpenProblemsLib.D_CombLine

open OpenProblemsLib.D_CombLine

/-- A081199(n): the 5-th binomial transform of 0, 1, 0, 1, ... -/
def A081199 (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), n.choose j * 5 ^ (n - j) * (j % 2)

open scoped Classical in
theorem A081199_main (n : ℕ) :
    ((Finset.univ.powersetCard 4).filter (fun S : Finset (Fin n → Fin 4) =>
        Collinear ℝ ((fun x : Fin n → Fin 4 => fun j => ((x j : ℕ) : ℝ)) '' (S : Set _)))).card =
      A081199 n ∧
    ((Finset.univ.powersetCard 4).filter (fun S : Finset (Fin n → Fin 4) =>
        Collinear ℝ ((fun x : Fin n → Fin 4 => fun j => ((x j : ℕ) : ℝ)) '' (S : Set _)))).card =
      (6 ^ n - 4 ^ n) / 2 := by
  have h := card_collinear (n := n) (k := 4) (by norm_num)
  exact ⟨h.1, h.2⟩
