import Mathlib

/-
COM-C023 (Mathlib). Coman's conjecture 23: if p, q are prime and q^2 = 2p - 1, then pq is a
Fermat pseudoprime to base p + 1. README result: false at (p, q) = (5, 3) (15 and
6^14 ≡ 6 mod 15), true for every other pair.

Main theorem `C023_main`, with Mathlib's `Nat.FermatPsp n b` (n ∣ b^(n-1) - 1, n not prime,
n > 1):
* (5, 3) satisfies the hypotheses and 15 is not a base-6 Fermat pseudoprime;
* for all primes p, q with q^2 = 2p - 1 and (p, q) ≠ (5, 3), `Nat.FermatPsp (p * q) (p + 1)`.
`C023_conjecture_false` is the negation of the conjecture.

Proof of the second part (README argument). q ≠ 2 (parity) and q ≠ 3 (else p = 5), so
q = 2r + 1 with r ≥ 2 and p = 2r^2 + 2r + 1. Then pq - 1 = (q - 1)(p + r + 1). Modulo p the base
is 1. Modulo q, q ∤ p + 1 (as 2(p + 1) = q^2 + 3 and q ≠ 3), so Fermat's little theorem
(`Nat.ModEq.pow_card_sub_one_eq_one`) gives (p + 1)^(q-1) ≡ 1. p ≠ q, so the two congruences
combine (`Nat.modEq_and_modEq_iff_modEq_mul`).

Outside Lean: nothing.
-/

theorem C023_counterexample :
    Nat.Prime 5 ∧ Nat.Prime 3 ∧ 3 ^ 2 = 2 * 5 - 1 ∧ ¬ Nat.FermatPsp (5 * 3) (5 + 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro h
  have h1 : ¬ (15 ∣ 6 ^ 14 - 1) := by decide
  exact h1 h.1

theorem C023_rest (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : q ^ 2 = 2 * p - 1)
    (hne : (p, q) ≠ (5, 3)) : Nat.FermatPsp (p * q) (p + 1) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  -- q is odd: q = 2 would give 4 = 2p - 1.
  --
  have hqodd : q % 2 = 1 := by
    rcases Nat.even_or_odd q with h | h
    · have := (Nat.Prime.even_iff hq).mp h
      subst this
      norm_num at hpq
      omega
    · exact Nat.odd_iff.mp h
  obtain ⟨r, rfl⟩ : ∃ r, q = 2 * r + 1 := ⟨q / 2, by omega⟩
  have hsq : (2 * r + 1) ^ 2 = 4 * (r * r) + 4 * r + 1 := by ring
  have hpr : p = 2 * (r * r) + 2 * r + 1 := by omega
  -- q ≠ 3, since q = 3 forces p = 5.
  --
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hne (by rw [hpr])
  have hr2 : 2 ≤ r := by omega
  -- q does not divide p + 1.
  --
  have hndvd : ¬ (2 * r + 1) ∣ p + 1 := by
    intro h
    have h2 : (2 * r + 1) ∣ 2 * (p + 1) := Dvd.dvd.mul_left h 2
    have he : 2 * (p + 1) = (2 * r + 1) * (2 * r + 1) + 3 := by rw [hpr]; ring
    rw [he] at h2
    have h3 : (2 * r + 1) ∣ 3 := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp h2
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hcop_q : (p + 1).Coprime (2 * r + 1) :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd)
  have hferm := Nat.ModEq.pow_card_sub_one_eq_one hq hcop_q
  have hexp : p * (2 * r + 1) - 1 = (2 * r + 1 - 1) * (p + r + 1) := by
    rw [hpr]
    have : 2 * r + 1 - 1 = 2 * r := by omega
    rw [this]
    apply Nat.sub_eq_of_eq_add
    ring
  have hmodq : (p + 1) ^ (p * (2 * r + 1) - 1) ≡ 1 [MOD 2 * r + 1] := by
    rw [hexp, pow_mul]
    simpa using hferm.pow (p + r + 1)
  have hmodp : (p + 1) ^ (p * (2 * r + 1) - 1) ≡ 1 [MOD p] := by
    have h1 : p + 1 ≡ 1 [MOD p] := by
      simp [Nat.ModEq, Nat.add_mod_left]
    simpa using h1.pow (p * (2 * r + 1) - 1)
  have hpq_ne : p ≠ 2 * r + 1 := by
    intro h
    rw [h] at hpr
    nlinarith
  have hcop : p.Coprime (2 * r + 1) := (Nat.coprime_primes hp hq).mpr hpq_ne
  have hmod := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmodp, hmodq⟩
  refine ⟨?_, Nat.not_prime_mul (by omega) (by omega), ?_⟩
  · exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp hmod.symm
  · have : 2 * 5 ≤ p * (2 * r + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega

theorem C023_main :
    (Nat.Prime 5 ∧ Nat.Prime 3 ∧ 3 ^ 2 = 2 * 5 - 1 ∧ ¬ Nat.FermatPsp (5 * 3) (5 + 1)) ∧
    ∀ p q : ℕ, p.Prime → q.Prime → q ^ 2 = 2 * p - 1 → (p, q) ≠ (5, 3) →
      Nat.FermatPsp (p * q) (p + 1) :=
  ⟨C023_counterexample, C023_rest⟩

theorem C023_conjecture_false :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → q ^ 2 = 2 * p - 1 → Nat.FermatPsp (p * q) (p + 1) := by
  intro h
  obtain ⟨h5, h3, he, hn⟩ := C023_counterexample
  exact hn (h 5 3 h5 h3 he)
