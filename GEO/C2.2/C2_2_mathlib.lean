import OpenProblemsLib

/-
GEO-C2.2 (Mathlib). Croft–Falconer–Guy C2 (Moroń): in a squared rectangle whose sides are
relatively prime, is there always a square whose side is a perfect square?
README result: no; the simple perfect squared rectangle 799 × 689 of order 14 with squares
5, 7, 23, 28, 30, 37, 44, 67, 72, 220, 287, 292, 397, 402 has none.

Main theorem `C2_2_main`: the 14 squares `c22` tile [0, 799] × [0, 689] ⊆ ℝ² exactly
(`IsTiling`: positive sides, union of the closed squares = the closed rectangle, pairwise
disjoint interiors; `OpenProblemsLib.SquaredRect`), their sides are pairwise distinct,
gcd(799, 689) = 1, and no side is a perfect square (Mathlib `IsSquare`).
`C2_2_answer`: hence "every coprime squared rectangle has a square of square side" is false.

Outside Lean: nothing (the exact-cover step left outside by the core-Lean file `C2_2.lean`
is `tiling_of_check`). Simplicity of the squaring is not claimed in the theorem.
-/

open OpenProblemsLib.SquaredRect

def c22 : List Sq :=
  [⟨402, 0, 0⟩, ⟨397, 402, 0⟩, ⟨5, 402, 397⟩, ⟨28, 407, 397⟩, ⟨72, 435, 397⟩,
   ⟨292, 507, 397⟩, ⟨287, 0, 402⟩, ⟨67, 287, 402⟩, ⟨30, 354, 402⟩, ⟨23, 384, 402⟩,
   ⟨7, 384, 425⟩, ⟨44, 391, 425⟩, ⟨37, 354, 432⟩, ⟨220, 287, 469⟩]

theorem not_square_of_check (n : ℕ) (hn : n < 21 * 21)
    (h : (List.range 21).all (fun r => r * r != n) = true) : ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have hr : r < 21 := by nlinarith
  have := List.all_eq_true.mp h r (List.mem_range.mpr hr)
  simp at this

theorem C2_2_main :
    IsTiling 799 689 c22 ∧ (c22.map Sq.s).Nodup ∧ Nat.gcd 799 689 = 1 ∧
      ∀ q ∈ c22, ¬ IsSquare q.s := by
  refine ⟨tiling_of_check _ _ _ (by decide +kernel), by decide, by norm_num, ?_⟩
  intro q hq
  simp only [c22, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact not_square_of_check _ (by norm_num) (by decide)

theorem C2_2_answer :
    ¬ ∀ (W H : ℕ) (l : List Sq), IsTiling W H l → (l.map Sq.s).Nodup → Nat.gcd W H = 1 →
      ∃ q ∈ l, IsSquare q.s := by
  intro h
  obtain ⟨ht, hp, hg, hn⟩ := C2_2_main
  obtain ⟨q, hq, hs⟩ := h _ _ _ ht hp hg
  exact hn q hq hs
