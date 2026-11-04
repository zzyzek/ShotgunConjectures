import OpenProblemsLib

/-
COM-P022 (Mathlib). Coman's problem 22: are there Carmichael numbers 176n + 1 besides 2465
and 15841? README result: yes, 340561, 670033, 825265, 1615681, ...

Main theorem `P022_yes`: 340561, 670033, 825265 and 1615681 are Carmichael numbers of the
form 176n + 1 (and differ from 2465, 15841). Carmichael by Korselt's criterion (Mathlib),
primes by Pratt certificates checked by the kernel.

Outside Lean: nothing. The count "15 below 10^7" is not checked here.
(Generated from certificate/P022_mathlib.lean.in by tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨13, 2, [(2, 2), (3, 1)]⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨19, 2, [(2, 1), (3, 2)]⟩,
   ⟨11, 2, [(2, 1), (5, 1)]⟩,
   ⟨23, 5, [(2, 1), (11, 1)]⟩,
   ⟨37, 2, [(2, 2), (3, 2)]⟩,
   ⟨67, 2, [(2, 1), (3, 1), (11, 1)]⟩,
   ⟨73, 5, [(2, 3), (3, 2)]⟩,
   ⟨199, 3, [(2, 1), (3, 2), (11, 1)]⟩,
   ⟨353, 3, [(2, 5), (11, 1)]⟩]

theorem carmichael_340561 : Nat.IsCarmichael 340561 :=
  isCarmichael_of_carmichaelCheck 340561 [13, 17, 23, 67] cert (by decide +kernel)
theorem carmichael_670033 : Nat.IsCarmichael 670033 :=
  isCarmichael_of_carmichaelCheck 670033 [7, 13, 37, 199] cert (by decide +kernel)
theorem carmichael_825265 : Nat.IsCarmichael 825265 :=
  isCarmichael_of_carmichaelCheck 825265 [5, 7, 17, 19, 73] cert (by decide +kernel)
theorem carmichael_1615681 : Nat.IsCarmichael 1615681 :=
  isCarmichael_of_carmichaelCheck 1615681 [23, 199, 353] cert (by decide +kernel)

theorem P022_yes : ∀ C ∈ [340561, 670033, 825265, 1615681],
    C.IsCarmichael ∧ (∃ n, C = 176 * n + 1) ∧ C ≠ 2465 ∧ C ≠ 15841 := by
  intro C hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · exact ⟨carmichael_340561, ⟨1935, rfl⟩, by norm_num, by norm_num⟩
  · exact ⟨carmichael_670033, ⟨3807, rfl⟩, by norm_num, by norm_num⟩
  · exact ⟨carmichael_825265, ⟨4689, rfl⟩, by norm_num, by norm_num⟩
  · exact ⟨carmichael_1615681, ⟨9180, rfl⟩, by norm_num, by norm_num⟩
