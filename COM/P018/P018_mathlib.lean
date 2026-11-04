import OpenProblemsLib

/-
COM-P018 (Mathlib). Coman's problem 18: are there Carmichael triples (C1, C2, C3) with
p(C1 − 1) − C2 = C3 for a prime p, besides (561, 1729, 8911)? README result: yes,
14293 * 560 − 8911 = 7995169 = 7 * 13 * 103 * 853, (C1, C2, C3) = (561, 8911, 7995169).

Main theorem `P018_yes`: there are a prime p and Carmichael numbers C1, C2, C3 with
p (C1 − 1) − C2 = C3 and (C1, C2, C3) ≠ (561, 1729, 8911). Carmichael by Korselt's
criterion (Mathlib), primes by Pratt certificates checked by the kernel.

Outside Lean: nothing. (Generated from certificate/P018_mathlib.lean.in by
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
   ⟨13, 2, [(2, 2), (3, 1)]⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨19, 2, [(2, 1), (3, 2)]⟩,
   ⟨67, 2, [(2, 1), (3, 1), (11, 1)]⟩,
   ⟨103, 5, [(2, 1), (3, 1), (17, 1)]⟩,
   ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩,
   ⟨853, 2, [(2, 2), (3, 1), (71, 1)]⟩,
   ⟨397, 5, [(2, 2), (3, 2), (11, 1)]⟩,
   ⟨14293, 6, [(2, 2), (3, 2), (397, 1)]⟩]

theorem carmichael_561 : Nat.IsCarmichael 561 :=
  isCarmichael_of_carmichaelCheck 561 [3, 11, 17] cert (by decide +kernel)
theorem carmichael_8911 : Nat.IsCarmichael 8911 :=
  isCarmichael_of_carmichaelCheck 8911 [7, 19, 67] cert (by decide +kernel)
theorem carmichael_7995169 : Nat.IsCarmichael 7995169 :=
  isCarmichael_of_carmichaelCheck 7995169 [7, 13, 103, 853] cert (by decide +kernel)
theorem prime_14293 : Nat.Prime 14293 :=
  prime_of_prattCertifies _ cert (by decide +kernel)

theorem P018_yes : ∃ p C1 C2 C3 : ℕ, p.Prime ∧ C1.IsCarmichael ∧ C2.IsCarmichael ∧
    C3.IsCarmichael ∧ p * (C1 - 1) - C2 = C3 ∧ (C1, C2, C3) ≠ (561, 1729, 8911) :=
  ⟨14293, 561, 8911, 7995169, prime_14293, carmichael_561, carmichael_8911, carmichael_7995169,
    by norm_num, by decide⟩
