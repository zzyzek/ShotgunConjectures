import OpenProblemsLib

/-
GEO-C2.1 (Mathlib). Croft–Falconer–Guy C2 (Moroń): in a squared rectangle, are there always
at least two squares surrounded by (four) larger ones? README result: no; the classical
order-9 perfect rectangle 61 × 69 (squares 2, 5, 7, 9, 16, 25, 28, 33, 36) has exactly one
surrounded square (side 2).

Main theorem `C2_1_main`: the nine squares `c21` tile [0, 61] × [0, 69] ⊆ ℝ² exactly
(`IsTiling`: positive sides, union of the closed squares = the closed rectangle, pairwise
disjoint interiors; `OpenProblemsLib.SquaredRect`), their sides are pairwise distinct
(perfect), and the list of surrounded squares is exactly [side 2].

"Surrounded" (README reading, most permissive): the square does not touch the boundary of
the rectangle, and every square sharing a boundary segment of positive length with it
(`adjacent`: an edge of one lies on the line of an edge of the other, with overlapping
open extents) is larger. These are definitions on the integer coordinates.

Outside Lean: nothing (the exact-cover step left outside by the core-Lean file `C2_1.lean`
is `tiling_of_check`). Moroń's original wording was not seen (README).
-/

open OpenProblemsLib.SquaredRect

def touchesBoundary (W H : ℕ) (q : Sq) : Bool :=
  q.x == 0 || q.y == 0 || q.x + q.s == W || q.y + q.s == H

/-- p and q share a boundary segment of positive length. -/
def adjacent (p q : Sq) : Bool :=
  ((p.x + p.s == q.x || q.x + q.s == p.x) && (max p.y q.y < min (p.y + p.s) (q.y + q.s))) ||
  ((p.y + p.s == q.y || q.y + q.s == p.y) && (max p.x q.x < min (p.x + p.s) (q.x + q.s)))

/-- q does not touch the boundary and every square adjacent to it is larger. -/
def surrounded (W H : ℕ) (l : List Sq) (q : Sq) : Bool :=
  !touchesBoundary W H q && l.all (fun p => !adjacent p q || q.s < p.s)

def c21 : List Sq :=
  [⟨2, 36, 34⟩, ⟨5, 33, 36⟩, ⟨7, 38, 34⟩, ⟨9, 36, 25⟩, ⟨16, 45, 25⟩,
   ⟨25, 36, 0⟩, ⟨28, 33, 41⟩, ⟨33, 0, 36⟩, ⟨36, 0, 0⟩]

theorem C2_1_main :
    IsTiling 61 69 c21 ∧ (c21.map Sq.s).Nodup ∧
      (c21.filter (surrounded 61 69 c21)).map Sq.s = [2] :=
  ⟨tiling_of_check _ _ _ (by decide +kernel), by decide, by decide⟩
