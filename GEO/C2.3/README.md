# CFG C2: a rectangle with two perfect squarings sharing no square size

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section C2. Moroń asked whether some rectangle can be squared in two distinct
ways with no square occurring in both squarings. ("Probably so.")

**Result.** Yes. The 593 × 422 rectangle has the perfect squarings
{2, 22, 37, 39, 41, 43, 80, 164, 178, 200, 207, 215, 222} and
{18, 38, 49, 67, 72, 85, 103, 116, 154, 175, 192, 230, 247}, both of order 13, with no common
size.

**Argument.** Direct check of both tilings.

**Evidence.**
- Lean (Mathlib): [`C2_3_mathlib.lean`](C2_3_mathlib.lean) proves `C2_3_main`: both lists tile [0, 593] × [0, 422] ⊆ ℝ² exactly (union of closed squares = closed rectangle, disjoint interiors; `OpenProblemsLib.SquaredRect.tiling_of_check`), each perfect, no common size. This closes the exact-cover step. Outside Lean: nothing.
- Lean: [`C2_3.lean`](C2_3.lean) (from `../open-problems/lean/Rectangles.lean`): both
  placements inside 593 × 422 with disjoint interiors and full area, each perfect, sizes
  disjoint (no axioms). Outside Lean: the standard step "inside the rectangle + pairwise disjoint interiors + total
area W·H ⇒ exact cover" (all corners are integers, so an uncovered unit cell would leave area
missing); the cell-by-cell cover was also checked in Python by the scan.
- `certificate/witnesses.json` (coordinates; its W/H labels are swapped), `pairs.py`.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`C2_3_mathlib.lean`](C2_3_mathlib.lean)).
**Prior art.** Known: pairs of perfect squarings of one rectangle with no common square ('totally different' conformal rectangles) go back to Brooks–Smith–Stone–Tutte 1940 (§7.2, §9; [pdf](https://carlo-hamalainen.net/stuff/Brooks,%20Smith,%20Stone,%20Tutte%20-%20The%20dissection%20of%20rectangles%20into%20squares%20(1940).pdf)) and are the standard ingredient of perfect squared squares (Canad. J. Math. notes on low-order perfect squared squares). Our 593 × 422 pair is one more instance. The BSST scan was read only through its summary. 2026-11-04.
