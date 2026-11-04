# OEIS A081201: collinear 6-tuples in the 6^n grid

**Source.** [A081201](https://oeis.org/A081201) (7th binomial transform of 0,1,0,1,…), comment by R. H. Hardin
(2010): "Conjecture (verified up to a(9)): Number of collinear 6-tuples of points in a 6 X 6 X ... n-dimensional
cubic grid." (OEIS text, CC BY-SA 4.0.)

**Result.** True: both equal ((8)^n − 6^n)/2.

**Argument.** The m-th binomial transform of 0,1,0,1,… is Σ_{j odd} C(n,j) m^(n−j) = ((m+1)^n − (m−1)^n)/2,
here m = 7. Now take 6 collinear points of {1..6}^n on a line x = a + t·v. In a coordinate with v_i ≠ 0
the 6 points have 6 distinct values in {1..6}, i.e. all of them; so the parameters form an arithmetic
progression and every coordinate is constant, runs 1..6, or runs 6..1 along it. These are the
combinatorial lines of the 6^n tic-tac-toe board: choose for each coordinate a constant (6 ways), up or
down, exclude all-constant, and identify a line with its reversal: ((8)^n − 6^n)/2.

**Evidence.**
- `certificate/check.py`: enumerates all lines through pairs of points (so non-grid collinear sets would be
  counted too) and counts 6-subsets for k = 4, 5, 6 and n ≤ 3; matches both formulas.
- Lean (Mathlib): [`A081201_mathlib.lean`](A081201_mathlib.lean), `A081201_main`: for every n, the number of 6-element subsets of {0..5}^n that are `Collinear ℝ` (in ℝ^n) equals Σ_j C(n,j) 7^(n-j) [j odd] and (8^n - 6^n)/2 (library module `lib/OpenProblemsLib/D_CombLine.lean`). Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).
**Prior art.** Known: collinear 6-sets in the 6^n grid are the winning lines of 6^n tic-tac-toe, counted by Moser's formula ((k+2)^n - k^n)/2 (see [Golomb-Hales 2002](https://library.slmath.org/books/Book42/files/golomb.pdf), Patashnik 1980). [A081201](https://oeis.org/A081201) still has Hardin's conjecture. Searched OEIS entry, references and history, web. Checked 2026-11-04.
