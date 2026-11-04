/-
OEIS A215462: number of ordered decompositions of 2n into two odd nonprimes
(1 counts as nonprime). Conjecture 1: a(n) ≠ 0 for n > 19. True: pick
c ∈ {9, 25, 35} with 2n - c ≡ 0 (mod 3) (possible since 9, 25, 35 are 0, 1, 2
mod 3); for n ≥ 22, 2n - c ≥ 9 is an odd multiple of 3, hence nonprime.
n = 20, 21: 40 = 15 + 25, 42 = 15 + 27.
Conjecture 2 (a(n) > A215461(n) > A002372(n) for large n) is argued in the
README (prime number theorem / Chebyshev and a sieve upper bound); not here.

Checked here (core Lean): `witness` for every n > 19 (omega), conjecture 1.
Not checked here: conjecture 2; that 9, 25, 35 and odd multiples of 3 that are
≥ 9 are nonprime (they have the factor 3 or 5).
-/

theorem witness (n : Nat) (h : 19 < n) :
    ∃ c d, (c = 9 ∨ c = 15 ∨ c = 25 ∨ c = 35) ∧ c + d = 2 * n ∧ 3 ∣ d ∧ 9 ≤ d ∧ d % 2 = 1 := by
  rcases Nat.lt_or_ge n 22 with h22 | h22
  · have : n = 20 ∨ n = 21 := by omega
    rcases this with rfl | rfl
    · exact ⟨25, 15, by omega, by omega, by decide, by omega, by omega⟩
    · exact ⟨15, 27, by omega, by omega, by decide, by omega, by omega⟩
  · have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    have : (2 * n - 9) % 3 = 0 ∨ (2 * n - 25) % 3 = 0 ∨ (2 * n - 35) % 3 = 0 := by
      rcases hr with hr | hr | hr
      · left; omega
      · right; right; omega
      · right; left; omega
    rcases this with h3 | h3 | h3
    · exact ⟨9, 2 * n - 9, by omega, by omega, Nat.dvd_of_mod_eq_zero h3, by omega, by omega⟩
    · exact ⟨25, 2 * n - 25, by omega, by omega, Nat.dvd_of_mod_eq_zero h3, by omega, by omega⟩
    · exact ⟨35, 2 * n - 35, by omega, by omega, Nat.dvd_of_mod_eq_zero h3, by omega, by omega⟩
