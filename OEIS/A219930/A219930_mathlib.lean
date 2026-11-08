/-
A219930: n such that phi(n) is a new lower bound for phi, i.e. phi(m) >= phi(n)
for all m >= n, n being the least number with that property and that value.

Checked here: no odd n > 3 has the lower-bound property
  `A219930LowerBound n : ∀ m, n < m → φ n ≤ φ m`.
Hence every member of A219930 other than 1 and 3 is even (the second OEIS
conjecture). The membership condition "least n with this phi value" is not
needed and is not formalised.

Not checked here: divisibility of large members by 3 and 5 (README,
certificate/moves.py and certificate/cert5.py).
-/
import Mathlib


/-- phi(n) is a lower bound for phi on all larger integers. -/
def A219930LowerBound (n : ℕ) : Prop := ∀ m, n < m → Nat.totient n ≤ Nat.totient m

/-- phi(p * N) ≥ (p - 1) * phi(N) for a prime p. -/
lemma A219930_totient_prime_mul_ge {p N : ℕ} (hp : p.Prime) :
    (p - 1) * Nat.totient N ≤ Nat.totient (p * N) := by
  by_cases h : p ∣ N
  · rw [Nat.totient_mul_of_prime_of_dvd hp h]
    exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
  · have hc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).2 h
    rw [Nat.totient_mul hc, Nat.totient_prime hp]

/-- phi(s * N) ≤ s * phi(N) for a prime s. -/
lemma A219930_totient_prime_mul_le {s N : ℕ} (hs : s.Prime) :
    Nat.totient (s * N) ≤ s * Nat.totient N := by
  by_cases h : s ∣ N
  · rw [Nat.totient_mul_of_prime_of_dvd hs h]
  · have hc : Nat.Coprime s N := (Nat.Prime.coprime_iff_not_dvd hs).2 h
    rw [Nat.totient_mul hc, Nat.totient_prime hs]
    exact Nat.mul_le_mul_right _ (Nat.sub_le s 1)

/-- An odd n with a prime factor p ≥ 5 is not a lower bound:
  m = 2 * s * (n / p) with s a Bertrand prime in ((p-1)/2, p-1]. -/
lemma A219930_not_lowerBound_of_prime_ge5 {n p : ℕ} (hodd : Odd n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ n) : ¬ A219930LowerBound n := by
  intro hL
  obtain ⟨N, rfl⟩ := hpn
  have hN0 : N ≠ 0 := by rintro rfl; simp at hodd
  have hNodd : Odd N := (Nat.odd_mul.1 hodd).2
  obtain ⟨s, hs, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ((p - 1) / 2) (by omega)
  -- s ≠ p - 1 because p - 1 is even and at least 4
  have hp2 : p % 2 = 1 := (hp.eq_one_or_self_of_dvd 2 |>.mt (by omega) |> fun _ => by
    rcases hp.eq_two_or_odd with h | h <;> omega)
  have hsne : s ≠ p - 1 := by
    intro h
    have := hs.eq_two_or_odd
    omega
  have hs2 : 2 * s > p := by omega
  have hsp : s + 1 < p := by omega
  have hNpos : 0 < Nat.totient N := Nat.totient_pos.2 (Nat.pos_of_ne_zero hN0)
  have hcop : Nat.Coprime 2 (s * N) := by
    have hsodd : Odd s := hs.eq_two_or_odd'.resolve_left (by omega)
    exact (Nat.coprime_two_left).2 (Nat.odd_mul.2 ⟨hsodd, hNodd⟩)
  have hm := hL (2 * (s * N)) (by nlinarith [Nat.pos_of_ne_zero hN0])
  rw [Nat.totient_mul hcop, Nat.totient_two, one_mul] at hm
  have h1 := A219930_totient_prime_mul_ge (N := N) hp
  have h2 := A219930_totient_prime_mul_le (N := N) hs
  have : s * Nat.totient N < (p - 1) * Nat.totient N :=
    Nat.mul_lt_mul_of_pos_right (by omega) hNpos
  omega

/-- 3^k with k ≥ 2 is not a lower bound: m = 4 * 3^(k-1). -/
lemma A219930_not_lowerBound_pow3 {k : ℕ} (hk : 2 ≤ k) : ¬ A219930LowerBound (3 ^ k) := by
  intro hL
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hpos : 0 < 3 ^ j := by positivity
  have e1 : (3:ℕ) ^ (j + 2) = 9 * 3 ^ j := by ring
  have e2 : (3:ℕ) ^ (j + 1) = 3 * 3 ^ j := by ring
  have hm := hL (4 * 3 ^ (j + 1)) (by rw [e1, e2]; omega)
  have hc : Nat.Coprime 4 (3 ^ (j + 1)) := by
    apply Nat.Coprime.pow_right; norm_num
  rw [Nat.totient_mul hc, Nat.totient_prime_pow Nat.prime_three (by omega),
    Nat.totient_prime_pow Nat.prime_three (by omega)] at hm
  have h4 : Nat.totient 4 = 2 := by decide
  rw [h4] at hm
  have e3 : (3:ℕ) ^ (j + 2 - 1) = 3 * 3 ^ j := by
    rw [show j + 2 - 1 = j + 1 by omega]; ring
  have e4 : (3:ℕ) ^ (j + 1 - 1) = 3 ^ j := by rw [show j + 1 - 1 = j by omega]
  rw [e3, e4] at hm
  omega

/-- Main theorem: no odd n > 3 has the lower-bound property. -/
theorem A219930_odd_not_lowerBound {n : ℕ} (hodd : Odd n) (h3 : 3 < n) : ¬ A219930LowerBound n := by
  by_cases hbig : ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ n
  · obtain ⟨p, hp, hp5, hpn⟩ := hbig
    exact A219930_not_lowerBound_of_prime_ge5 hodd hp hp5 hpn
  · push Not at hbig
    have hn0 : n ≠ 0 := by omega
    have hall : ∀ {d : ℕ}, d.Prime → d ∣ n → d = 3 := by
      intro d hd hdn
      have h5 : d < 5 := by
        by_contra h; exact hbig d hd (by omega) hdn
      have h2 : d ≠ 2 := by
        rintro rfl; exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdn)
      interval_cases d <;> simp_all <;> norm_num at hd
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hn0 hall
    generalize hk : n.primeFactorsList.length = k at hpow
    subst hpow
    have hk2 : 2 ≤ k := by
      by_contra hk'
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact A219930_not_lowerBound_pow3 hk2

/-- Members of A219930 other than 1 and 3 are even (a member has the
lower-bound property). -/
theorem A219930_members_even {n : ℕ} (hL : A219930LowerBound n) (h : n ≠ 1 ∧ n ≠ 3) : Even n := by
  by_contra he
  have hodd : Odd n := Nat.not_even_iff_odd.1 he
  have h3 : 3 < n := by
    rcases hodd with ⟨t, rfl⟩
    rcases Nat.lt_or_ge t 2 with ht | ht
    · interval_cases t <;> simp_all
    · omega
  exact A219930_odd_not_lowerBound hodd h3 hL

