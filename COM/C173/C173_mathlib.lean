import OpenProblemsLib

/-
COM-C173 and COM-C174 (Mathlib; also covers P115). Coman's conjecture 173: every Carmichael
number divisible by 37 and 73 is ≡ 1 (mod 10). Conjecture 174: every Carmichael number
divisible by 37 and 73 has a prime factor ≡ 23 (mod 30). README results: both false,
294409 = 37 * 73 * 109 (≡ 9 mod 10; factors ≡ 7, 13, 19 mod 30).

Main theorems `C173_false` and `C174_false`: the negations of the two conjectures.
Carmichael by Korselt's criterion (Mathlib), primes by Pratt certificates checked by the
kernel; every prime factor of 294409 is 37, 73 or 109 (`mem_of_prime_dvd_prod`).

Outside Lean: nothing. (Generated from certificate/C173_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨37, 2, [(2, 2), (3, 2)]⟩,
   ⟨73, 5, [(2, 3), (3, 2)]⟩,
   ⟨109, 6, [(2, 2), (3, 3)]⟩]

theorem carmichael_C : Nat.IsCarmichael 294409 :=
  isCarmichael_of_carmichaelCheck 294409 [37, 73, 109] cert (by decide +kernel)

theorem primes_C : ∀ p ∈ [37, 73, 109], Nat.Prime p :=
  primes_of_prattCertifiesAll _ cert (by decide +kernel)

theorem C173_false : ¬ ∀ C : ℕ, C.IsCarmichael → 37 ∣ C → 73 ∣ C → C % 10 = 1 := by
  intro h
  have := h 294409 carmichael_C (by norm_num) (by norm_num)
  norm_num at this

theorem C174_false : ¬ ∀ C : ℕ, C.IsCarmichael → 37 ∣ C → 73 ∣ C →
    ∃ q, q.Prime ∧ q ∣ C ∧ q % 30 = 23 := by
  intro h
  obtain ⟨q, hq, hd, hr⟩ := h 294409 carmichael_C (by norm_num) (by norm_num)
  have := mem_of_prime_dvd_prod [37, 73, 109] primes_C hq (by simpa using hd)
  simp at this
  rcases this with rfl | rfl | rfl <;> norm_num at hr
