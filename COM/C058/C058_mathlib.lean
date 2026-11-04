import OpenProblemsLib

/-
COM-C058 (Mathlib). Coman, conjecture 58: every 2-Poulet number is (q·2^a·3^b·5^c ± 1)·2^n + 1
with n ≥ 1, a, b, c ≥ 0 and q a prime, a prime square or a semiprime.
README result: false, 514447 = 359 · 1433.

Main theorem `C058_main`: 514447 is a 2-Poulet number (Mathlib `Nat.FermatPsp 514447 2`,
= 359 · 1433 with both factors prime) and there are no natural numbers q, a, b, c, n with
n ≥ 1, q prime, the square of a prime, or a product of two primes, and
514447 = (q·2^a·3^b·5^c + 1)·2^n + 1 or 514447 = (q·2^a·3^b·5^c - 1)·2^n + 1.
Proof: 514446 = 2 · 257223 with 257223 odd forces n = 1; then q·2^a·3^b·5^c is
257222 = 2·7·19·967 or 257224 = 2³·11·37·79; the primes 7, 19, 967 (resp. 11, 37, 79) are
prime to 2^a·3^b·5^c, so all three divide q, impossible for q with at most two prime factors.

Outside Lean: nothing.
-/

open OpenProblemsLib

/-- `q` is a prime, a prime square or a semiprime (at most two prime factors with
multiplicity, at least one). -/
def AtMostTwoPrimes (q : ℕ) : Prop :=
  q.Prime ∨ (∃ r, r.Prime ∧ q = r ^ 2) ∨ (∃ r s, r.Prime ∧ s.Prime ∧ q = r * s)

theorem no_three (q r₁ r₂ r₃ : ℕ) (h : AtMostTwoPrimes q) (p₁ : r₁.Prime) (p₂ : r₂.Prime)
    (p₃ : r₃.Prime) (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃)
    (d₁ : r₁ ∣ q) (d₂ : r₂ ∣ q) (d₃ : r₃ ∣ q) : False := by
  have key : ∀ r s, r.Prime → s.Prime → q = r * s → False := by
    intro r s hr hs hq
    subst hq
    have f : ∀ t, t.Prime → t ∣ r * s → t = r ∨ t = s := by
      intro t ht hd
      rcases (Nat.Prime.dvd_mul ht).mp hd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq ht hr).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq ht hs).mp h)
    rcases f _ p₁ d₁ with a | a <;> rcases f _ p₂ d₂ with b | b <;>
      rcases f _ p₃ d₃ with c | c <;> omega
  rcases h with hq | ⟨r, hr, hq⟩ | ⟨r, s, hr, hs, hq⟩
  · have := (Nat.prime_dvd_prime_iff_eq p₁ hq).mp d₁
    have := (Nat.prime_dvd_prime_iff_eq p₂ hq).mp d₂
    omega
  · exact key r r hr hr (by rw [hq]; ring)
  · exact key r s hr hs hq

theorem cop (t a b c : ℕ) (ht : t.Prime) (h2 : t ≠ 2) (h3 : t ≠ 3) (h5 : t ≠ 5) :
    Nat.Coprime t (2 ^ a * 3 ^ b * 5 ^ c) := by
  have g : ∀ u, u.Prime → t ≠ u → Nat.Coprime t u := fun u hu hne =>
    (Nat.coprime_primes ht hu).mpr hne
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right
    ((g 2 Nat.prime_two h2).pow_right a) ((g 3 Nat.prime_three h3).pow_right b))
    ((g 5 Nat.prime_five h5).pow_right c)

theorem no_q (q a b c X : ℕ) (hq : AtMostTwoPrimes q) (hX : q * 2 ^ a * 3 ^ b * 5 ^ c = X)
    (r₁ r₂ r₃ : ℕ) (p₁ : r₁.Prime) (p₂ : r₂.Prime) (p₃ : r₃.Prime)
    (s₁ : r₁ ≠ 2 ∧ r₁ ≠ 3 ∧ r₁ ≠ 5) (s₂ : r₂ ≠ 2 ∧ r₂ ≠ 3 ∧ r₂ ≠ 5)
    (s₃ : r₃ ≠ 2 ∧ r₃ ≠ 3 ∧ r₃ ≠ 5) (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃)
    (d₁ : r₁ ∣ X) (d₂ : r₂ ∣ X) (d₃ : r₃ ∣ X) : False := by
  have e : X = q * (2 ^ a * 3 ^ b * 5 ^ c) := by rw [← hX]; ring
  rw [e] at d₁ d₂ d₃
  exact no_three q r₁ r₂ r₃ hq p₁ p₂ p₃ h12 h13 h23
    ((cop _ a b c p₁ s₁.1 s₁.2.1 s₁.2.2).dvd_of_dvd_mul_right d₁)
    ((cop _ a b c p₂ s₂.1 s₂.2.1 s₂.2.2).dvd_of_dvd_mul_right d₂)
    ((cop _ a b c p₃ s₃.1 s₃.2.1 s₃.2.2).dvd_of_dvd_mul_right d₃)

theorem n_eq_one (Y n : ℕ) (hn : 1 ≤ n) (h : 514447 = Y * 2 ^ n + 1) : Y = 257223 := by
  rcases Nat.lt_or_ge n 2 with h1 | h1
  · have : n = 1 := by omega
    subst this; omega
  · have : 4 ∣ 2 ^ n := by
      have := Nat.pow_dvd_pow 2 h1
      simpa using this
    obtain ⟨k, hk⟩ := this
    have : 4 ∣ 514446 := ⟨Y * k, by rw [show 514446 = Y * 2 ^ n by omega, hk]; ring⟩
    norm_num at this

theorem p7 : Nat.Prime 7 := by norm_num
theorem p19 : Nat.Prime 19 := by norm_num
theorem p967 : Nat.Prime 967 := by norm_num
theorem p11 : Nat.Prime 11 := by norm_num
theorem p37 : Nat.Prime 37 := by norm_num
theorem p79 : Nat.Prime 79 := by norm_num

theorem C058_main :
    Nat.FermatPsp 514447 2 ∧ 514447 = 359 * 1433 ∧ Nat.Prime 359 ∧ Nat.Prime 1433 ∧
      ¬ ∃ q a b c n : ℕ, 1 ≤ n ∧ AtMostTwoPrimes q ∧
        (514447 = (q * 2 ^ a * 3 ^ b * 5 ^ c + 1) * 2 ^ n + 1 ∨
         514447 = (q * 2 ^ a * 3 ^ b * 5 ^ c - 1) * 2 ^ n + 1) := by
  refine ⟨fermatPsp_of_pspCheck _ _ 359 (by decide +kernel), by norm_num, by norm_num,
    by norm_num, ?_⟩
  rintro ⟨q, a, b, c, n, hn, hq, h | h⟩
  · have hY := n_eq_one _ n hn h
    have hX : q * 2 ^ a * 3 ^ b * 5 ^ c = 257222 := by omega
    exact no_q q a b c _ hq hX 7 19 967 p7 p19 p967 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
  · have hY := n_eq_one _ n hn h
    have hX : q * 2 ^ a * 3 ^ b * 5 ^ c = 257224 := by omega
    exact no_q q a b c _ hq hX 11 37 79 p11 p37 p79 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
