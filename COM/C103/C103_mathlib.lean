import OpenProblemsLib

/-
COM-C103 (Mathlib; also covers P047). Coman's conjecture 103: if a Carmichael number C is
not a Harshad number (its digit sum does not divide it) and its digital root s is not 1,
then every prime factor d ≠ 3 of C is n(s − 1) ± 1 for some n ≥ 1. README result: false,
62745 = 3 * 5 * 47 * 89 (digit sum 24 ∤ 62745, s = 6, d = 5).

Main theorem `C103_false`: the negation, with digit sum `(Nat.digits 10 C).sum` and digital
root `1 + (C - 1) % 9`. Carmichael by Korselt's criterion (Mathlib), primes by Pratt
certificates checked by the kernel.

Outside Lean: nothing. The count "79 failures" is not checked here.
(Generated from certificate/C103_mathlib.lean.in by tools/lean_expand.py.)
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

theorem C103_false : ¬ ∀ C : ℕ, C.IsCarmichael → ¬ (Nat.digits 10 C).sum ∣ C →
    1 + (C - 1) % 9 ≠ 1 →
    ∀ d, d.Prime → d ∣ C → d ≠ 3 →
      ∃ n, 1 ≤ n ∧ (d = n * ((1 + (C - 1) % 9) - 1) + 1 ∨ d = n * ((1 + (C - 1) % 9) - 1) - 1) := by
  intro h
  have := h 62745 carmichael_C (by norm_num) (by norm_num) 5 (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨n, hn, h1 | h1⟩ := this <;> norm_num at h1 <;> omega
