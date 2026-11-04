import OpenProblemsLib

/-
COM-P016 (Mathlib). Coman's problem 16 asks about the conjecture that every Carmichael
number is ≡ 1 (mod 10), ≡ 1 (mod 12) or ≡ 1 (mod 14). README result: false,
62745 = 3 * 5 * 47 * 89 is ≡ 5, 9, 11 modulo 10, 12, 14.

Main theorem `P016_false`: the negation of that conjecture. Carmichael by Korselt's
criterion (Mathlib), primes by Pratt certificates checked by the kernel.

Outside Lean: nothing. (Generated from certificate/P016_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨11, 2, [(2, 1), (5, 1)]⟩,
   ⟨23, 5, [(2, 1), (11, 1)]⟩,
   ⟨47, 5, [(2, 1), (23, 1)]⟩,
   ⟨89, 3, [(2, 3), (11, 1)]⟩]

theorem carmichael_C : Nat.IsCarmichael 62745 :=
  isCarmichael_of_carmichaelCheck 62745 [3, 5, 47, 89] cert (by decide +kernel)

theorem P016_false : ¬ ∀ C : ℕ, C.IsCarmichael → C % 10 = 1 ∨ C % 12 = 1 ∨ C % 14 = 1 := by
  intro h
  have := h 62745 carmichael_C
  norm_num at this
