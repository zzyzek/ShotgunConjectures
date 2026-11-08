/-
Guy B36 (k = 3): every solution n >= 3 of phi(n+3) = phi(n) + phi(3) has the form
n = 2 p^a or n + 3 = 2 p^a with p prime, p = 3 (mod 4), a >= 1.

Checked here: `B36_2_reduction` (the reduction), with the characterisation
`B36_2_totient_mod4` of m >= 3 with phi(m) = 2 (mod 4).
Also checked: `B36_2_lehmer` (the case n = 2p gives a composite m = 2p + 3 with
phi(m) | m - 1, against Lehmer's totient conjecture). Not checked here: all
computations (certificate/).
-/
import Mathlib

open Nat

lemma B36_2_four_dvd_of_prime_one {m p : ℕ} (_hm : m ≠ 0) (hp : p.Prime) (h1 : p % 4 = 1)
    (hpm : p ∣ m) : 4 ∣ φ m := by
  have := Nat.totient_dvd_of_dvd hpm
  rw [Nat.totient_prime hp] at this
  exact dvd_trans (by omega : 4 ∣ p - 1) this

lemma B36_2_four_dvd_of_two_odd {m p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpm : p ∣ m) (hqm : q ∣ m) : 4 ∣ φ m := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hd : p * q ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpm hqm
  have := Nat.totient_dvd_of_dvd hd
  rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq] at this
  have ho1 := hp.eq_two_or_odd
  have ho2 := hq.eq_two_or_odd
  have e1 : 2 ∣ p - 1 := by omega
  have e2 : 2 ∣ q - 1 := by omega
  exact dvd_trans (by
    obtain ⟨x, hx⟩ := e1; obtain ⟨y, hy⟩ := e2
    rw [hx, hy]; exact ⟨x * y, by ring⟩) this

lemma B36_2_four_dvd_of_eight {m : ℕ} (h : 8 ∣ m) : 4 ∣ φ m := by
  have := Nat.totient_dvd_of_dvd h
  have h8 : φ 8 = 4 := by decide
  rwa [h8] at this

lemma B36_2_four_dvd_of_four_odd {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h4 : 4 ∣ m)
    (hpm : p ∣ m) : 4 ∣ φ m := by
  have hcop : Nat.Coprime 4 p := by
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    simpa using Nat.Coprime.pow_left 2 this
  have hd : 4 * p ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h4 hpm
  have := Nat.totient_dvd_of_dvd hd
  rw [Nat.totient_mul hcop, Nat.totient_prime hp] at this
  have h4' : φ 4 = 2 := by decide
  rw [h4'] at this
  have ho := hp.eq_two_or_odd
  exact dvd_trans (by obtain ⟨x, hx⟩ : 2 ∣ p - 1 := by omega
                      rw [hx]; exact ⟨x, by ring⟩) this

/-- phi(2k) ≤ k. -/
lemma B36_2_totient_two_mul_le (k : ℕ) : φ (2 * k) ≤ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | hk
    · rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp at hj; subst hj; simp
      · have h2 : 2 ∣ 2 * j := dvd_mul_right 2 j
        have : 2 * k = 2 * (2 * j) := by omega
        rw [this, Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2]
        have := ih j (by omega)
        omega
    · have hc : Nat.Coprime 2 k := (Nat.coprime_two_left).2 hk
      rw [Nat.totient_mul hc, Nat.totient_two, one_mul]
      exact Nat.totient_le k

/-- An odd number m ≠ 1 whose only prime factor is p is a power p^a with a ≥ 1. -/
lemma B36_2_pow_of_unique {m p : ℕ} (hm : m ≠ 0) (hm1 : m ≠ 1)
    (h : ∀ {d : ℕ}, d.Prime → d ∣ m → d = p) : ∃ a, 1 ≤ a ∧ m = p ^ a := by
  have := Nat.eq_prime_pow_of_unique_prime_dvd hm h
  refine ⟨m.primeFactorsList.length, ?_, this⟩
  rcases Nat.eq_zero_or_pos m.primeFactorsList.length with h0 | h0
  · rw [h0, pow_zero] at this; exact absurd this hm1
  · exact h0

/-- Characterisation: m ≥ 3 and phi(m) = 2 (mod 4) give m = 4, p^a or 2 p^a with p = 3 (mod 4). -/
theorem B36_2_totient_mod4 {m : ℕ} (hm : 3 ≤ m) (h : φ m % 4 = 2) :
    m = 4 ∨ ∃ p a, p.Prime ∧ p % 4 = 3 ∧ 1 ≤ a ∧ (m = p ^ a ∨ m = 2 * p ^ a) := by
  have hm0 : m ≠ 0 := by omega
  have no4 : ¬ 4 ∣ φ m := by omega
  by_cases hodd : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ m
  · obtain ⟨p, hp, hp2, hpm⟩ := hodd
    have hp3 : p % 4 = 3 := by
      have ho := hp.eq_two_or_odd
      rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1 | h3
      · exact absurd (B36_2_four_dvd_of_prime_one hm0 hp h1 hpm) no4
      · exact h3
    have huniq : ∀ {d : ℕ}, d.Prime → d ≠ 2 → d ∣ m → d = p := by
      intro d hd hd2 hdm
      by_contra hne
      exact no4 (B36_2_four_dvd_of_two_odd hd hp hne hd2 hp2 hdm hpm)
    have h4 : ¬ 4 ∣ m := fun h4 => no4 (B36_2_four_dvd_of_four_odd hp hp2 h4 hpm)
    right
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | hmo
    · -- m = 2k with k odd
      have hk' : m = 2 * k := by omega
      have hkodd : ¬ 2 ∣ k := by
        intro h2; exact h4 (by obtain ⟨t, ht⟩ := h2; exact ⟨t, by omega⟩)
      have hk0 : k ≠ 0 := by omega
      have hk1 : k ≠ 1 := by
        intro h1; have hpk : p ∣ 2 * k := hk' ▸ hpm
        rw [h1] at hpk
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpk
        exact hp2 this
      obtain ⟨a, ha, hka⟩ := B36_2_pow_of_unique hk0 hk1 (fun {d} hd hdk => by
        have hd2 : d ≠ 2 := by rintro rfl; exact hkodd hdk
        exact huniq hd hd2 (hk' ▸ dvd_mul_of_dvd_right hdk 2))
      exact ⟨p, a, hp, hp3, ha, Or.inr (by rw [hk', hka])⟩
    · have hm1 : m ≠ 1 := by omega
      obtain ⟨a, ha, hma⟩ := B36_2_pow_of_unique hm0 hm1 (fun {d} hd hdm => by
        have hd2 : d ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.2 hmo) (even_iff_two_dvd.2 hdm)
        exact huniq hd hd2 hdm)
      exact ⟨p, a, hp, hp3, ha, Or.inl hma⟩
  · push Not at hodd
    left
    have h2only : ∀ {d : ℕ}, d.Prime → d ∣ m → d = 2 := by
      intro d hd hdm; by_contra hne; exact hodd d hd hne hdm
    have hm1 : m ≠ 1 := by omega
    obtain ⟨b, hb, hmb⟩ := B36_2_pow_of_unique hm0 hm1 h2only
    have hb2 : 2 ≤ b := by
      by_contra hlt
      have : b = 1 := by omega
      subst this; simp at hmb; omega
    rcases (by omega : b = 2 ∨ 3 ≤ b) with rfl | hb3
    · simpa using hmb
    · exfalso
      apply no4
      apply B36_2_four_dvd_of_eight
      rw [hmb]
      exact (Nat.pow_dvd_pow 2 hb3)

/-- Main theorem: solutions of phi(n+3) = phi(n) + phi(3) with n ≥ 3 lie in the
two families n = 2p^a and n + 3 = 2p^a, p prime, p = 3 (mod 4), a ≥ 1. -/
theorem B36_2_reduction {n : ℕ} (hn : 3 ≤ n) (h : φ (n + 3) = φ n + φ 3) :
    ∃ p a, p.Prime ∧ p % 4 = 3 ∧ 1 ≤ a ∧ (n = 2 * p ^ a ∨ n + 3 = 2 * p ^ a) := by
  have h3 : φ 3 = 2 := by decide
  rw [h3] at h
  have e1 : Even (φ n) := Nat.totient_even (by omega)
  have e2 : Even (φ (n + 3)) := Nat.totient_even (by omega)
  obtain ⟨x, hx⟩ := e1
  obtain ⟨y, hy⟩ := e2
  rcases (by omega : φ n % 4 = 2 ∨ φ (n + 3) % 4 = 2) with h1 | h2
  · rcases B36_2_totient_mod4 hn h1 with h4 | ⟨p, a, hp, hp3, ha, hpow | hpow⟩
    · exfalso
      subst h4
      have a7 : φ 7 = 6 := by decide
      have a4 : φ 4 = 2 := by decide
      rw [show (4:ℕ) + 3 = 7 from rfl, a7, a4] at h
      omega
    · -- n = p^a is odd, so n + 3 is even and phi(n+3) ≤ (n+3)/2: too small
      exfalso
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hphi : φ n = p ^ b * (p - 1) := by rw [hpow, Nat.totient_prime_pow_succ hp]
      have hodd : Odd n := hpow ▸ (Odd.pow (by rcases hp.eq_two_or_odd with h | h <;> [omega; exact Nat.odd_iff.2 h]))
      obtain ⟨k, hk⟩ : ∃ k, n + 3 = 2 * k := by
        obtain ⟨t, ht⟩ := hodd; exact ⟨t + 2, by omega⟩
      have hle := B36_2_totient_two_mul_le k
      rw [← hk] at hle
      have hP : 1 ≤ p ^ b := Nat.one_le_pow _ _ hp.pos
      have hpa : n = p ^ b * p := by rw [hpow, pow_succ]
      have hp3' : 3 ≤ p := by omega
      have : p ^ b * (p - 1) + 2 ≤ k := by omega
      have h5 : 2 * (p ^ b * (p - 1)) + 4 ≤ p ^ b * p + 3 := by omega
      have h6 : p ^ b * (p - 1) = p ^ b * p - p ^ b := by
        rw [Nat.mul_sub, mul_one]
      have h7 : p ^ b * p ≥ 3 * p ^ b := by nlinarith
      omega
    · exact ⟨p, a, hp, hp3, ha, Or.inl hpow⟩
  · rcases B36_2_totient_mod4 (by omega) h2 with h4 | ⟨p, a, hp, hp3, ha, hpow | hpow⟩
    · omega
    · -- n + 3 = p^a is odd, so n is even and phi(n) ≤ n/2: too small
      exfalso
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hphi : φ (n + 3) = p ^ b * (p - 1) := by rw [hpow, Nat.totient_prime_pow_succ hp]
      have hodd : Odd (n + 3) := hpow ▸ (Odd.pow (by rcases hp.eq_two_or_odd with h | h <;> [omega; exact Nat.odd_iff.2 h]))
      obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := by
        obtain ⟨t, ht⟩ := hodd; exact ⟨t - 1, by omega⟩
      have hle := B36_2_totient_two_mul_le k
      rw [← hk] at hle
      have hP : 1 ≤ p ^ b := Nat.one_le_pow _ _ hp.pos
      have hpa : n + 3 = p ^ b * p := by rw [hpow, pow_succ]
      have hp3' : 3 ≤ p := by omega
      have h6 : p ^ b * (p - 1) = p ^ b * p - p ^ b := by
        rw [Nat.mul_sub, mul_one]
      have h7 : p ^ b * p ≥ 3 * p ^ b := by nlinarith
      omega
    · exact ⟨p, a, hp, hp3, ha, Or.inr hpow⟩

/-- Family n = 2p: m = 2p + 3 would be a composite with phi(m) ∣ m - 1,
a counterexample to Lehmer's totient conjecture. -/
theorem B36_2_lehmer {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (h : φ (2 * p + 3) = φ (2 * p) + φ 3) :
    ¬ (2 * p + 3).Prime ∧ φ (2 * p + 3) ∣ 2 * p + 3 - 1 := by
  have hp2 : p ≠ 2 := by omega
  have hc : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have h3 : φ 3 = 2 := by decide
  rw [Nat.totient_mul hc, Nat.totient_two, one_mul, Nat.totient_prime hp, h3] at h
  have hp1 : 3 ≤ p := by omega
  refine ⟨fun hq => ?_, ?_⟩
  · rw [Nat.totient_prime hq] at h; omega
  · rw [h]; exact ⟨2, by omega⟩
