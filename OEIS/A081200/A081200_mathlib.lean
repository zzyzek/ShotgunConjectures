/-
OEIS A081200, Mathlib proof.

A081200(n) = Σ_j C(n, j)·6^(n-j)·[j odd] (6-th binomial transform of
0, 1, 0, 1, ...). Conjecture (R. H. Hardin, 2010): a(n) is the number of
collinear 5-tuples of points in the 5 × 5 × ... × 5 n-dimensional cubic grid.

Reading: a collinear 5-tuple is a 5-element set of grid points lying on one
line (Mathlib `Collinear ℝ` of the set). The grid is {0, ..., 4}^n
(`Fin n → Fin 5`, embedded in ℝ^n); translating to {1, ..., 5}^n does not
change collinearity.

Main theorem `A081200_main`: for every n, the number of 5-element subsets S of
the grid with `Collinear ℝ` (image of S in ℝ^n) equals A081200(n), and equals
(7^n - 5^n)/2. This is the README result.

Proof (library `OpenProblemsLib.D_CombLine`, general k ≥ 2): a collinear
k-set of {0..k-1}^n is a combinatorial line (each coordinate constant,
increasing or decreasing along it, not all constant), and each line has
exactly two such descriptions. Nothing is outside Lean.
-/
import Mathlib
import OpenProblemsLib.D_CombLine

open OpenProblemsLib.D_CombLine

/-- A081200(n): the 6-th binomial transform of 0, 1, 0, 1, ... -/
def A081200 (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), n.choose j * 6 ^ (n - j) * (j % 2)

open scoped Classical in
theorem A081200_main (n : ℕ) :
    ((Finset.univ.powersetCard 5).filter (fun S : Finset (Fin n → Fin 5) =>
        Collinear ℝ ((fun x : Fin n → Fin 5 => fun j => ((x j : ℕ) : ℝ)) '' (S : Set _)))).card =
      A081200 n ∧
    ((Finset.univ.powersetCard 5).filter (fun S : Finset (Fin n → Fin 5) =>
        Collinear ℝ ((fun x : Fin n → Fin 5 => fun j => ((x j : ℕ) : ℝ)) '' (S : Set _)))).card =
      (7 ^ n - 5 ^ n) / 2 := by
  have h := card_collinear (n := n) (k := 5) (by norm_num)
  exact ⟨h.1, h.2⟩
