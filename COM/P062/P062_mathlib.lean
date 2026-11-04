import OpenProblemsLib

/-
COM-P062 (Mathlib). Coman's problem 62: are there p, C1, C2, C3 besides
(59, 561, 1729, 2465) with p, p + C1 − 1, p + C2 − 1 prime, C1, C2 Carmichael and the sum
p + (p + C1 − 1) + (p + C2 − 1) = C3 a Carmichael number? README result: yes,
(1812443, 561, 6601, 5444489).

Main theorem `P062_yes`: such a quadruple exists other than (59, 561, 1729, 2465).
Carmichael by Korselt's criterion (Mathlib), primes by Pratt certificates checked by the
kernel.

Outside Lean: nothing. (Generated from certificate/P062_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨11, 2, [(2, 1), (5, 1)]⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨23, 5, [(2, 1), (11, 1)]⟩,
   ⟨29, 2, [(2, 2), (7, 1)]⟩,
   ⟨41, 6, [(2, 3), (5, 1)]⟩,
   ⟨197, 2, [(2, 2), (7, 2)]⟩,
   ⟨953, 3, [(2, 3), (7, 1), (17, 1)]⟩,
   ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
   ⟨31249, 23, [(2, 4), (3, 2), (7, 1), (31, 1)]⟩,
   ⟨1812443, 2, [(2, 1), (29, 1), (31249, 1)]⟩,
   ⟨109, 6, [(2, 2), (3, 3)]⟩,
   ⟨16787, 2, [(2, 1), (7, 1), (11, 1), (109, 1)]⟩,
   ⟨302167, 5, [(2, 1), (3, 2), (16787, 1)]⟩,
   ⟨1813003, 3, [(2, 1), (3, 1), (302167, 1)]⟩,
   ⟨11369, 3, [(2, 3), (7, 2), (29, 1)]⟩,
   ⟨909521, 6, [(2, 4), (5, 1), (11369, 1)]⟩,
   ⟨1819043, 2, [(2, 1), (909521, 1)]⟩]

theorem carmichael_561 : Nat.IsCarmichael 561 :=
  isCarmichael_of_carmichaelCheck 561 [3, 11, 17] cert (by decide +kernel)
theorem carmichael_6601 : Nat.IsCarmichael 6601 :=
  isCarmichael_of_carmichaelCheck 6601 [7, 23, 41] cert (by decide +kernel)
theorem carmichael_5444489 : Nat.IsCarmichael 5444489 :=
  isCarmichael_of_carmichaelCheck 5444489 [29, 197, 953] cert (by decide +kernel)
theorem primes_p : ∀ p ∈ [1812443, 1813003, 1819043], Nat.Prime p :=
  primes_of_prattCertifiesAll _ cert (by decide +kernel)

theorem P062_yes : ∃ p C1 C2 C3 : ℕ, p.Prime ∧ (p + C1 - 1).Prime ∧ (p + C2 - 1).Prime ∧
    C1.IsCarmichael ∧ C2.IsCarmichael ∧ C3.IsCarmichael ∧
    p + (p + C1 - 1) + (p + C2 - 1) = C3 ∧ (p, C1, C2, C3) ≠ (59, 561, 1729, 2465) := by
  refine ⟨1812443, 561, 6601, 5444489, primes_p _ (by simp), primes_p _ (by simp),
    primes_p _ (by simp), carmichael_561, carmichael_6601, carmichael_5444489, by norm_num,
    by decide⟩
