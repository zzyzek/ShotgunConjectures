import OpenProblemsLib

/-
COM-C089 (Mathlib; also covers P004). Coman's conjecture 89: every Carmichael number
divisible by 7 and 13 is 91(18k + 1) or 91(18k + 13). README result: false,
9890881 = 7 * 11 * 13 * 41 * 241 = 91 * 108691 with 108691 ≡ 7 (mod 18).

Main theorem `C089_false`: the negation of the conjecture (k natural), witness 9890881.
Carmichael by Korselt's criterion (Mathlib), primes by Pratt certificates checked by the
kernel.

Outside Lean: nothing. The count "62 failures below 1e13" is not checked here.
(Generated from certificate/C089_mathlib.lean.in by tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨11, 2, [(2, 1), (5, 1)]⟩,
   ⟨13, 2, [(2, 2), (3, 1)]⟩,
   ⟨41, 6, [(2, 3), (5, 1)]⟩,
   ⟨241, 7, [(2, 4), (3, 1), (5, 1)]⟩]

theorem carmichael_C : Nat.IsCarmichael 9890881 :=
  isCarmichael_of_carmichaelCheck 9890881 [7, 11, 13, 41, 241] cert (by decide +kernel)

theorem C089_false : ¬ ∀ C : ℕ, C.IsCarmichael → 7 ∣ C → 13 ∣ C →
    ∃ k : ℕ, C = 91 * (18 * k + 1) ∨ C = 91 * (18 * k + 13) := by
  intro h
  obtain ⟨k, hk | hk⟩ := h 9890881 carmichael_C (by norm_num) (by norm_num) <;> omega
