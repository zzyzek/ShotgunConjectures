import OpenProblemsLib

/-
COM-P040 (Mathlib). Coman's problem 40: for every Carmichael number C coprime to 15, is some
C² − 2C − 30k prime? Same question for C1² − 2C2 − 30k. README result: no to both;
C = 162401 gives C(C − 2) ≡ 9 (mod 30), so every positive C² − 2C − 30k is a multiple of 3
above 3; likewise 1729² − 2 * 162401 ≡ 9 (mod 30).

Main theorem `P040_no`: (1) 162401 is a Carmichael number coprime to 15 and
C² − 2C − 30k is prime for no natural k; (2) 1729 and 162401 are Carmichael numbers coprime
to 15 and 1729² − 2 * 162401 − 30k is prime for no natural k. Natural subtraction: values
with 30k beyond the first term are 0, which is not prime either, so this covers exactly the
positive values of the README. Carmichael by Korselt's criterion (Mathlib), primes by Pratt
certificates checked by the kernel.

Outside Lean: nothing. (Generated from certificate/P040_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨13, 2, [(2, 2), (3, 1)]⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨19, 2, [(2, 1), (3, 2)]⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨41, 6, [(2, 3), (5, 1)]⟩,
   ⟨29, 2, [(2, 2), (7, 1)]⟩,
   ⟨233, 3, [(2, 3), (29, 1)]⟩]

theorem carmichael_162401 : Nat.IsCarmichael 162401 :=
  isCarmichael_of_carmichaelCheck 162401 [17, 41, 233] cert (by decide +kernel)
theorem carmichael_1729 : Nat.IsCarmichael 1729 :=
  isCarmichael_of_carmichaelCheck 1729 [7, 13, 19] cert (by decide +kernel)

theorem three_dvd_not_prime (x : ℕ) (h3 : 3 ∣ x) (hx : x ≠ 3) : ¬ x.Prime := fun hp =>
  hx ((Nat.Prime.eq_one_or_self_of_dvd hp 3 h3).resolve_left (by norm_num)).symm

theorem P040_no :
    (Nat.IsCarmichael 162401 ∧ Nat.Coprime 162401 15 ∧
      ∀ k : ℕ, ¬ (162401 ^ 2 - 2 * 162401 - 30 * k).Prime) ∧
    (Nat.IsCarmichael 1729 ∧ Nat.IsCarmichael 162401 ∧ Nat.Coprime 1729 15 ∧
      Nat.Coprime 162401 15 ∧ ∀ k : ℕ, ¬ (1729 ^ 2 - 2 * 162401 - 30 * k).Prime) := by
  refine ⟨⟨carmichael_162401, by norm_num, fun k => three_dvd_not_prime _ ?_ ?_⟩,
    ⟨carmichael_1729, carmichael_162401, by norm_num, by norm_num,
      fun k => three_dvd_not_prime _ ?_ ?_⟩⟩ <;> norm_num <;> omega
