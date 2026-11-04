/-
OEIS A215461: number of ordered decompositions of 2n into one odd prime and
one odd nonprime (1 counts as nonprime). Conjecture: a(n) ≠ 0 for n > 5.
True: for n > 5 one of 2n - 3, 2n - 5, 2n - 7 is divisible by 3 and exceeds 3,
hence an odd nonprime, and 3, 5, 7 are prime.

Checked here (core Lean): `witness` for every n > 5 (omega).
Not checked here: nothing (a multiple of 3 larger than 3 is not prime).
-/

theorem witness (n : Nat) (h : 5 < n) :
    ∃ p, (p = 3 ∨ p = 5 ∨ p = 7) ∧ 3 ∣ 2 * n - p ∧ 3 < 2 * n - p ∧ (2 * n - p) % 2 = 1 := by
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have : (2 * n - 3) % 3 = 0 ∨ (2 * n - 5) % 3 = 0 ∨ (2 * n - 7) % 3 = 0 := by
    rcases hr with hr | hr | hr
    · left; omega
    · right; left; omega
    · right; right; omega
  rcases this with h3 | h3 | h3
  · exact ⟨3, by omega, Nat.dvd_of_mod_eq_zero h3, by omega, by omega⟩
  · exact ⟨5, by omega, Nat.dvd_of_mod_eq_zero h3, by omega, by omega⟩
  · exact ⟨7, by omega, Nat.dvd_of_mod_eq_zero h3, by omega, by omega⟩
