import OpenProblemsLib

/-
OEIS A215672 (Fermat pseudoprimes to base 2 with three prime factors).
Conjecture (Marius Coman, entry): any Poulet number P with three or more prime
divisors has a prime divisor q with P = q*((r+1)*q - r), r a natural number.
Counterexample (Charles R Greathouse IV, entry, Dec 2014): P = 617093 = 43 * 113 * 127.

Main theorem `A215672_false`: the conjecture, stated for all P with
Nat.FermatPsp P 2 and at least three distinct prime factors, is false.
Ingredients: `P_psp` (lib `pspCheck`, kernel powMod), `P_primeFactors`
(primeFactors 617093 = {43, 113, 127}), `no_q` (for each of the three primes the
equation is linear in r and has no natural solution; `omega`).
Not checked in this file: minimality of 617093 (certificate/search.py).
-/

open OpenProblemsLib

namespace A215672

theorem P_psp : Nat.FermatPsp 617093 2 := fermatPsp_of_pspCheck 617093 2 43 (by decide +kernel)

theorem hps : ∀ x ∈ [43, 113, 127], x.Prime := by norm_num

theorem P_primeFactors : (617093 : ℕ).primeFactors = {43, 113, 127} := by
  have := primeFactors_eq_of_primes [43, 113, 127] hps
  rw [show [43, 113, 127].prod = 617093 by norm_num] at this
  rw [this]; decide

theorem no_q (q r : ℕ) (hq : q.Prime) (hqP : q ∣ 617093) : 617093 ≠ q * ((r + 1) * q - r) := by
  have hmem : q ∈ [43, 113, 127] :=
    mem_of_prime_dvd_prod _ hps hq (by rw [show [43, 113, 127].prod = 617093 by norm_num]; exact hqP)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> omega

theorem A215672_false : ¬ ∀ P : ℕ, Nat.FermatPsp P 2 → 3 ≤ P.primeFactors.card →
    ∃ q, q.Prime ∧ q ∣ P ∧ ∃ r : ℕ, P = q * ((r + 1) * q - r) := by
  intro h
  obtain ⟨q, hq, hqP, r, hr⟩ := h 617093 P_psp (by rw [P_primeFactors]; decide)
  exact no_q q r hq hqP hr
