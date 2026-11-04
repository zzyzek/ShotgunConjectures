/-
Coman C101, Mathlib proof.

Main theorem `C101_main`: if p and p + 2 are both prime, then every prime
factor r of p (p + 2) + 1729 is 2, 3, or congruent to 1, 7, 13 or 19
modulo 30.

This is the README result (Coman's conjecture 101) verbatim. Proof as in
the README: p = 3 gives 1744 = 2^4 * 109; for p ≥ 5, p = 6j + 5 and
p (p + 2) + 1729 = 36 ((j + 1)^2 + 48). A prime r ≥ 5 dividing
x^2 + 48 has r ≡ 1 (mod 3): w = (x - 4)/8 satisfies w^3 = 1, w ≠ 1 in
ZMod r, and Fermat's little theorem w^(r-1) = 1 forces 3 ∣ r - 1
(this replaces the appeal to quadratic reciprocity for -3). r = 5 never
divides x^2 + 48 (squares mod 5 are 0, 1, 4).

Not checked: nothing; the whole statement is proved here.
-/
import Mathlib

theorem C101_prime_dvd_small {r n : ℕ} (hr : r.Prime) (hn : n ∣ 2 ^ 6 * 3 ^ 2)
    (hrn : r ∣ n) : r = 2 ∨ r = 3 := by
  have h := hrn.trans hn
  rcases (Nat.Prime.dvd_mul hr).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h))

theorem C101_mod_three (r x : ℕ) (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3)
    (hd : r ∣ x ^ 2 + 48) : r % 3 = 1 := by
  have := Fact.mk hr
  have hx : ((x : ZMod r)) ^ 2 = -48 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at this
    linear_combination this
  -- A natural number n that is 0 in ZMod r and divides 2^6 * 3^2 forces r ∈ {2, 3}.
  --
  have small : ∀ n : ℕ, n ∣ 2 ^ 6 * 3 ^ 2 → (n : ZMod r) ≠ 0 := by
    intro n hn h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    rcases C101_prime_dvd_small hr hn h0 with h | h
    · exact h2 h
    · exact h3 h
  have h8 : (8 : ZMod r) ≠ 0 := by exact_mod_cast small 8 (by norm_num)
  set w : ZMod r := ((x : ZMod r) - 4) / 8 with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, div_pow, div_eq_one_iff_eq (pow_ne_zero 3 h8)]
    linear_combination ((x : ZMod r) - 12) * hx
  have hw1 : w ≠ 1 := by
    intro h
    rw [hw, div_eq_one_iff_eq h8] at h
    have hx12 : (x : ZMod r) = 12 := by linear_combination h
    rw [hx12] at hx
    have : ((192 : ℕ) : ZMod r) = 0 := by push_cast; linear_combination hx
    exact small 192 (by norm_num) this
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw3
    simp at hw3
  have hferm := ZMod.pow_card_sub_one_eq_one hw0
  by_contra hne
  have hr3 : r % 3 ≠ 0 := by
    intro h0
    have : 3 ∣ r := Nat.dvd_of_mod_eq_zero h0
    exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp this).symm
  have hr2 := hr.two_le
  have hsplit : r - 1 = 3 * ((r - 2) / 3) + 1 := by omega
  rw [hsplit, pow_add, pow_mul, hw3, one_pow, one_mul, pow_one] at hferm
  exact hw1 hferm

theorem C101_not_five (x : ℕ) : ¬ 5 ∣ x ^ 2 + 48 := by
  intro h
  have h5 := Nat.mod_eq_zero_of_dvd h
  have hx := Nat.mod_lt x (by norm_num : 5 > 0)
  rw [Nat.add_mod, Nat.pow_mod] at h5
  interval_cases hj : x % 5 <;> simp at h5

theorem C101_main (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (r : ℕ) (hr : r.Prime)
    (hd : r ∣ p * (p + 2) + 1729) :
    r = 2 ∨ r = 3 ∨ r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 13 ∨ r % 30 = 19 := by
  by_cases h2 : r = 2
  · exact Or.inl h2
  by_cases h3 : r = 3
  · exact Or.inr (Or.inl h3)
  right; right
  by_cases hp3 : p = 3
  · subst hp3
    have h1744 : (3 * (3 + 2) + 1729 : ℕ) = 2 ^ 4 * 109 := by norm_num
    rw [h1744] at hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (hr.dvd_of_dvd_pow h)) h2
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h
      subst this
      norm_num
  -- p ≥ 5 and p ≡ 5 (mod 6).
  --
  have hpo : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · subst h; norm_num at hp2
    · exact h
  have hp30 : p % 3 ≠ 0 := by
    intro h0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
  have hp31 : p % 3 ≠ 1 := by
    intro h1
    have h3d : 3 ∣ p + 2 := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp2).mp h3d
    have := hp.two_le
    omega
  obtain ⟨j, hj⟩ : ∃ j, p = 6 * j + 5 := ⟨p / 6, by omega⟩
  have hN : p * (p + 2) + 1729 = 36 * ((j + 1) ^ 2 + 48) := by subst hj; ring
  rw [hN] at hd
  have hd' : r ∣ (j + 1) ^ 2 + 48 := by
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · rcases C101_prime_dvd_small hr (by norm_num : 36 ∣ 2 ^ 6 * 3 ^ 2) h with h | h
      · exact absurd h h2
      · exact absurd h h3
    · exact h
  have hm3 := C101_mod_three r (j + 1) hr h2 h3 hd'
  have hm5 : r % 5 ≠ 0 := by
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hr).mp (Nat.dvd_of_mod_eq_zero h0)
    subst this
    exact C101_not_five (j + 1) hd'
  have hm2 : r % 2 = 1 := by
    rcases hr.eq_two_or_odd with h | h
    · exact absurd h h2
    · exact h
  omega
