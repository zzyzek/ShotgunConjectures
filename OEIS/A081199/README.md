# OEIS A081199: collinear 4-tuples in the 4^n grid

**Source.** [A081199](https://oeis.org/A081199) (5th binomial transform of 0,1,0,1,…), comment by R. H. Hardin
(2010): "Conjecture (verified up to a(9)): Number of collinear 4-tuples of points in a 4 X 4 X ... n-dimensional
cubic grid." (OEIS text, CC BY-SA 4.0.)

**Result.** True: both equal ((6)^n − 4^n)/2.

**Argument.** The m-th binomial transform of 0,1,0,1,… is Σ_{j odd} C(n,j) m^(n−j) = ((m+1)^n − (m−1)^n)/2,
here m = 5. Now take 4 collinear points of {1..4}^n on a line x = a + t·v. In a coordinate with v_i ≠ 0
the 4 points have 4 distinct values in {1..4}, i.e. all of them; so the parameters form an arithmetic
progression and every coordinate is constant, runs 1..4, or runs 4..1 along it. These are the
combinatorial lines of the 4^n tic-tac-toe board: choose for each coordinate a constant (4 ways), up or
down, exclude all-constant, and identify a line with its reversal: ((6)^n − 4^n)/2.

**Evidence.**
- `certificate/check.py`: enumerates all lines through pairs of points (so non-grid collinear sets would be
  counted too) and counts 4-subsets for k = 4, 5, 6 and n ≤ 3; matches both formulas.
- Lean (Mathlib): [`A081199_mathlib.lean`](A081199_mathlib.lean), `A081199_main`: for every n, the number of 4-element subsets of {0..3}^n that are `Collinear ℝ` (in ℝ^n) equals Σ_j C(n,j) 5^(n-j) [j odd] and (6^n - 4^n)/2. The classification of collinear k-sets as combinatorial lines (k ≥ 2) is the library module `lib/OpenProblemsLib/D_CombLine.lean`. Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).
**Prior art.** Known: collinear 4-sets in the 4^n grid are the winning lines of 4^n tic-tac-toe, counted by Moser's formula ((k+2)^n - k^n)/2 (see [Golomb-Hales 2002](https://library.slmath.org/books/Book42/files/golomb.pdf), Patashnik 1980). [A081199](https://oeis.org/A081199) still has Hardin's conjecture. Searched OEIS entry, references and history, web. Checked 2026-11-04.
