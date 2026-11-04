import OpenProblemsLib

/-
COM-C044 (Mathlib). Coman's conjecture 44 says (in particular) that no Carmichael number
C ≡ 1 (mod 10) whose prime factors are all ≡ 1 (mod 10) has the shape
(30a+1)(30b+1)(30c+11). README result: false as stated, witness
1044430736441 = 41 * 191 * 281 * 521 * 911 = (30*261+1)(30*4880+1)(30*30+11).

Main theorem `C044_false`: there is a Carmichael number C with C % 10 = 1, every prime factor
≡ 1 (mod 10), and C = (30a+1)(30b+1)(30c+11) for some naturals a, b, c. This is the negation
of the "in particular" clause, hence of the conjecture. Carmichael by Korselt's criterion
(Mathlib), primes by Pratt certificates checked by the kernel.

Outside Lean: nothing. The count of such numbers below 1e13 is not checked here.
(Generated from certificate/C044_mathlib.lean.in by tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨41, 6, [(2, 3), (5, 1)]⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨19, 2, [(2, 1), (3, 2)]⟩,
   ⟨191, 19, [(2, 1), (5, 1), (19, 1)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨281, 3, [(2, 3), (5, 1), (7, 1)]⟩,
   ⟨13, 2, [(2, 2), (3, 1)]⟩,
   ⟨521, 3, [(2, 3), (5, 1), (13, 1)]⟩,
   ⟨911, 17, [(2, 1), (5, 1), (7, 1), (13, 1)]⟩]

theorem carmichael_C : Nat.IsCarmichael 1044430736441 :=
  isCarmichael_of_carmichaelCheck 1044430736441 [41, 191, 281, 521, 911] cert (by decide +kernel)

theorem primes_C : ∀ p ∈ [41, 191, 281, 521, 911], Nat.Prime p :=
  primes_of_prattCertifiesAll _ cert (by decide +kernel)

theorem C044_false : ∃ C : ℕ, C.IsCarmichael ∧ C % 10 = 1 ∧
    (∀ p, p.Prime → p ∣ C → p % 10 = 1) ∧
    ∃ a b c : ℕ, C = (30 * a + 1) * (30 * b + 1) * (30 * c + 11) := by
  refine ⟨1044430736441, carmichael_C, by norm_num, ?_, 261, 4880, 30, by norm_num⟩
  intro p hp hd
  have := mem_of_prime_dvd_prod [41, 191, 281, 521, 911] primes_C hp (by simpa using hd)
  simp at this
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
