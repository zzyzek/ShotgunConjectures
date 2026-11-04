# CFG C2: a perfect squared rectangle with only one square surrounded by larger ones

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section C2. Moroń asked whether in a squared rectangle there are always at
least two squares that are surrounded by (four) larger ones. ("Probably not.")

**Reading.** "Squared rectangle" read as perfect (all squares different); with repeated sizes
even a 2 × 1 rectangle of two unit squares has none. A square counts as surrounded (most
permissive reading) if it does not touch the boundary and every square sharing a boundary
segment of positive length with it is larger; every stricter reading gives a smaller count.
Moroń's original wording (Colloq. Math. 2 (1951) Problems 66–68) was not seen.

**Result.** No. The classical order-9 perfect rectangle 61 × 69 with squares 2, 5, 7, 9, 16,
25, 28, 33, 36 has exactly one surrounded square (side 2). (The smallest square of a perfect
squared rectangle is always surrounded, so 1 is the least possible count.)

**Argument.** The four squares not touching the boundary are 2, 5, 7, 9; each of 5, 7, 9 shares
an edge segment with the square 2 (along y = 36, x = 38, y = 34 respectively), so only 2 is
surrounded.

**Evidence.**
- Lean (Mathlib): [`C2_1_mathlib.lean`](C2_1_mathlib.lean) proves `C2_1_main`: the nine squares tile [0, 61] × [0, 69] ⊆ ℝ² exactly (union of the closed squares = the closed rectangle, pairwise disjoint interiors; `OpenProblemsLib.SquaredRect.tiling_of_check`, a column-by-column cover certificate plus a closure argument), the sides are distinct, and the surrounded squares are exactly [2]. This closes the exact-cover step. Outside Lean: nothing for the witness; the parenthetical remark that the smallest square is always surrounded is not formalised.
- Lean: [`C2_1.lean`](C2_1.lean) checks the placement (inside, disjoint interiors, total
  area, distinct sides) and computes the surrounded squares: exactly [2] (no axioms).
  Outside Lean: the standard step "inside the rectangle + pairwise disjoint interiors + total
area W·H ⇒ exact cover" (all corners are integers, so an uncovered unit cell would leave area
missing); the cell-by-cell cover was also checked in Python by the scan.
- `certificate/witness_order9.json` (coordinates), `gen.py`, `search.py` from the scan:
  423 of 7776 random perfect rectangles also have count 1.

**Review level.** `lean-proof`: the answer (a perfect squared rectangle with exactly one surrounded square) is proved in Lean + Mathlib ([`C2_1_mathlib.lean`](C2_1_mathlib.lean)).
**Prior art.** Not found stated anywhere; the witness is the classical 69 × 61 order-9 rectangle, so the answer is a short check (immediate, trivial). Searched: web on Moroń's problems and on surrounded squares, [BSST 1940](https://carlo-hamalainen.net/stuff/Brooks,%20Smith,%20Stone,%20Tutte%20-%20The%20dissection%20of%20rectangles%20into%20squares%20(1940).pdf), squaring.net. Moroń's original wording (Colloq. Math. 2 (1951) 60–61) not seen. 2026-11-04.
