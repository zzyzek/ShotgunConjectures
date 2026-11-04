import OpenProblemsLib

/-
GEO-C2.3 (Mathlib). Croft–Falconer–Guy C2 (Moroń): can some rectangle be squared in two
distinct ways with no square size occurring in both squarings? README result: yes; the
593 × 422 rectangle has the perfect squarings {2, 22, 37, 39, 41, 43, 80, 164, 178, 200, 207,
215, 222} and {18, 38, 49, 67, 72, 85, 103, 116, 154, 175, 192, 230, 247} with no common size.

Main theorem `C2_3_main`: both lists `c23a`, `c23b` tile [0, 593] × [0, 422] ⊆ ℝ² exactly
(`IsTiling`: positive sides, union of the closed squares = the closed rectangle, pairwise
disjoint interiors; `OpenProblemsLib.SquaredRect`), each has pairwise distinct sides
(perfect), and no side of one occurs in the other (so the two squarings are distinct).

Outside Lean: nothing (the exact-cover step left outside by the core-Lean file `C2_3.lean`
is `tiling_of_check`).
-/

open OpenProblemsLib.SquaredRect

def c23a : List Sq :=
  [⟨2, 341, 205⟩, ⟨22, 200, 222⟩, ⟨37, 341, 207⟩, ⟨39, 302, 205⟩, ⟨41, 302, 164⟩,
   ⟨43, 343, 164⟩, ⟨80, 222, 164⟩, ⟨164, 222, 0⟩, ⟨178, 200, 244⟩, ⟨200, 0, 222⟩,
   ⟨207, 386, 0⟩, ⟨215, 378, 207⟩, ⟨222, 0, 0⟩]

def c23b : List Sq :=
  [⟨18, 278, 85⟩, ⟨38, 363, 230⟩, ⟨49, 247, 103⟩, ⟨67, 296, 85⟩, ⟨72, 175, 103⟩,
   ⟨85, 278, 0⟩, ⟨103, 175, 0⟩, ⟨116, 247, 152⟩, ⟨154, 247, 268⟩, ⟨175, 0, 0⟩,
   ⟨192, 401, 230⟩, ⟨230, 363, 0⟩, ⟨247, 0, 175⟩]

theorem C2_3_main :
    IsTiling 593 422 c23a ∧ IsTiling 593 422 c23b ∧
      (c23a.map Sq.s).Nodup ∧ (c23b.map Sq.s).Nodup ∧
      ∀ p ∈ c23a, ∀ q ∈ c23b, p.s ≠ q.s := by
  refine ⟨tiling_of_check _ _ _ (by decide +kernel), tiling_of_check _ _ _ (by decide +kernel),
    by decide, by decide, ?_⟩
  have h : c23a.all (fun p => c23b.all (fun q => p.s != q.s)) = true := by decide
  intro p hp q hq
  have := List.all_eq_true.mp (List.all_eq_true.mp h p hp) q hq
  simpa using this
