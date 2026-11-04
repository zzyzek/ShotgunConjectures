# OEIS A081200: collinear 5-tuples in the 5^n grid

**Source.** [A081200](https://oeis.org/A081200) (6th binomial transform of 0,1,0,1,…), comment by R. H. Hardin
(2010): "Conjecture (verified up to a(9)): Number of collinear 5-tuples of points in a 5 X 5 X ... n-dimensional
cubic grid." (OEIS text, CC BY-SA 4.0.)

**Result.** True: both equal ((7)^n − 5^n)/2.

**Argument.** The m-th binomial transform of 0,1,0,1,… is Σ_{j odd} C(n,j) m^(n−j) = ((m+1)^n − (m−1)^n)/2,
here m = 6. Now take 5 collinear points of {1..5}^n on a line x = a + t·v. In a coordinate with v_i ≠ 0
the 5 points have 5 distinct values in {1..5}, i.e. all of them; so the parameters form an arithmetic
progression and every coordinate is constant, runs 1..5, or runs 5..1 along it. These are the
combinatorial lines of the 5^n tic-tac-toe board: choose for each coordinate a constant (5 ways), up or
down, exclude all-constant, and identify a line with its reversal: ((7)^n − 5^n)/2.

**Evidence.**
- `certificate/check.py`: enumerates all lines through pairs of points (so non-grid collinear sets would be
  counted too) and counts 5-subsets for k = 4, 5, 6 and n ≤ 3; matches both formulas.
- Lean (Mathlib): [`A081200_mathlib.lean`](A081200_mathlib.lean), `A081200_main`: for every n, the number of 5-element subsets of {0..4}^n that are `Collinear ℝ` (in ℝ^n) equals Σ_j C(n,j) 6^(n-j) [j odd] and (7^n - 5^n)/2 (library module `lib/OpenProblemsLib/D_CombLine.lean`). Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).
**Prior art.** Known: collinear 5-sets in the 5^n grid are the winning lines of 5^n tic-tac-toe, counted by Moser's formula ((k+2)^n - k^n)/2 (see [Golomb-Hales 2002](https://library.slmath.org/books/Book42/files/golomb.pdf), Patashnik 1980). [A081200](https://oeis.org/A081200) still has Hardin's conjecture. Searched OEIS entry, references and history, web. Checked 2026-11-04.
