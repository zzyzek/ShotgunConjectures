import OpenProblemsLib

/-
COM-P044 (Mathlib). Coman's problem 44: are there Carmichael numbers 561 + 272n besides
1105 and 2465? README result: yes, 75361, 162401, 278545, 340561, ...

Main theorem `P044_yes`: 75361, 162401, 278545 and 340561 are Carmichael numbers of the
form 561 + 272n (n natural) and differ from 1105 and 2465. Carmichael by Korselt's criterion
(Mathlib), primes by Pratt certificates checked by the kernel.

Outside Lean: nothing. (Generated from certificate/P044_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨11, 2, [(2, 1), (5, 1)]⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨13, 2, [(2, 2), (3, 1)]⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨23, 5, [(2, 1), (11, 1)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨29, 2, [(2, 2), (7, 1)]⟩,
   ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
   ⟨41, 6, [(2, 3), (5, 1)]⟩,
   ⟨67, 2, [(2, 1), (3, 1), (11, 1)]⟩,
   ⟨113, 3, [(2, 4), (7, 1)]⟩,
   ⟨233, 3, [(2, 3), (29, 1)]⟩]

theorem carmichael_75361 : Nat.IsCarmichael 75361 :=
  isCarmichael_of_carmichaelCheck 75361 [11, 13, 17, 31] cert (by decide +kernel)
theorem carmichael_162401 : Nat.IsCarmichael 162401 :=
  isCarmichael_of_carmichaelCheck 162401 [17, 41, 233] cert (by decide +kernel)
theorem carmichael_278545 : Nat.IsCarmichael 278545 :=
  isCarmichael_of_carmichaelCheck 278545 [5, 17, 29, 113] cert (by decide +kernel)
theorem carmichael_340561 : Nat.IsCarmichael 340561 :=
  isCarmichael_of_carmichaelCheck 340561 [13, 17, 23, 67] cert (by decide +kernel)

theorem P044_yes : ∀ C ∈ [75361, 162401, 278545, 340561],
    C.IsCarmichael ∧ (∃ n, C = 561 + 272 * n) ∧ C ≠ 1105 ∧ C ≠ 2465 := by
  intro C hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · exact ⟨carmichael_75361, ⟨275, rfl⟩, by norm_num, by norm_num⟩
  · exact ⟨carmichael_162401, ⟨595, rfl⟩, by norm_num, by norm_num⟩
  · exact ⟨carmichael_278545, ⟨1022, rfl⟩, by norm_num, by norm_num⟩
  · exact ⟨carmichael_340561, ⟨1250, rfl⟩, by norm_num, by norm_num⟩
