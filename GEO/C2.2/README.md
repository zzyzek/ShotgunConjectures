# CFG C2: a coprime perfect squared rectangle with no square of square side

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section C2. Moroń asked whether, in a squared rectangle whose sides are
relatively prime, there is always a square whose side is a perfect square. ("Probably not.")

**Result.** No. The simple perfect squared rectangle 799 × 689 (gcd 1) of order 14 with squares
5, 7, 23, 28, 30, 37, 44, 67, 72, 220, 287, 292, 397, 402 has no square whose side is a perfect
square. (The scan also found witnesses of orders 17 and 23.)

**Argument.** Direct check of the tiling and of the 14 sides.

**Evidence.**
- Lean (Mathlib): [`C2_2_mathlib.lean`](C2_2_mathlib.lean) proves `C2_2_main`: the 14 squares tile [0, 799] × [0, 689] ⊆ ℝ² exactly (union of closed squares = closed rectangle, disjoint interiors; `OpenProblemsLib.SquaredRect.tiling_of_check`), sides distinct, gcd(799, 689) = 1, no side a perfect square (Mathlib `IsSquare`); `C2_2_answer` negates the question. This closes the exact-cover step. Outside Lean: nothing.
- Lean: [`C2_2.lean`](C2_2.lean) (from `../open-problems/lean/Rectangles.lean`): placement
  inside 799 × 689, disjoint interiors, total area, distinct sides, gcd(799, 689) = 1, no side
  a perfect square (no axioms). Outside Lean: the standard step "inside the rectangle + pairwise disjoint interiors + total
area W·H ⇒ exact cover" (all corners are integers, so an uncovered unit cell would leave area
missing); the cell-by-cell cover was also checked in Python by the scan.
- `certificate/squared_rect_c2.py` (Kirchhoff search) and `verify_c2.py` (exact placement).

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`C2_2_mathlib.lean`](C2_2_mathlib.lean)).
**Prior art.** No source found that states the answer; any catalogue of low-order simple perfect rectangles (Bouwkamp–Duijvestijn–Medema 1960) contains such witnesses, so it is a lookup (immediate, trivial). Searched: web on Moroń's question, squaring.net. 2026-11-04.
