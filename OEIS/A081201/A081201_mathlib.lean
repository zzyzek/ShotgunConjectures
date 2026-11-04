/-
OEIS A081201, Mathlib proof.

A081201(n) = Σ_j C(n, j)·7^(n-j)·[j odd] (7-th binomial transform of
0, 1, 0, 1, ...). Conjecture (R. H. Hardin, 2010): a(n) is the number of
collinear 6-tuples of points in the 6 × 6 × ... × 6 n-dimensional cubic grid.

Reading: a collinear 6-tuple is a 6-element set of grid points lying on one
line (Mathlib `Collinear ℝ` of the set). The grid is {0, ..., 5}^n
(`Fin n → Fin 6`, embedded in ℝ^n); translating to {1, ..., 6}^n does not
change collinearity.

Main theorem `A081201_main`: for every n, the number of 6-element subsets S of
the grid with `Collinear ℝ` (image of S in ℝ^n) equals A081201(n), and equals
(8^n - 6^n)/2. This is the README result.

Proof (library `OpenProblemsLib.D_CombLine`, general k ≥ 2): a collinear
k-set of {0..k-1}^n is a combinatorial line (each coordinate constant,
increasing or decreasing along it, not all constant), and each line has
exactly two such descriptions. Nothing is outside Lean.
-/
import Mathlib
import OpenProblemsLib.D_CombLine

open OpenProblemsLib.D_CombLine

/-- A081201(n): the 7-th binomial transform of 0, 1, 0, 1, ... -/
def A081201 (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), n.choose j * 7 ^ (n - j) * (j % 2)

open scoped Classical in
theorem A081201_main (n : ℕ) :
    ((Finset.univ.powersetCard 6).filter (fun S : Finset (Fin n → Fin 6) =>
        Collinear ℝ ((fun x : Fin n → Fin 6 => fun j => ((x j : ℕ) : ℝ)) '' (S : Set _)))).card =
      A081201 n ∧
    ((Finset.univ.powersetCard 6).filter (fun S : Finset (Fin n → Fin 6) =>
        Collinear ℝ ((fun x : Fin n → Fin 6 => fun j => ((x j : ℕ) : ℝ)) '' (S : Set _)))).card =
      (8 ^ n - 6 ^ n) / 2 := by
  have h := card_collinear (n := n) (k := 6) (by norm_num)
  exact ⟨h.1, h.2⟩
