/-
OEIS A219543 (and A218755): denominators of Bernoulli numbers that are
≡ 3 (mod 9) (A219543), resp. ≡ 6 (mod 9) (A218755); both are subsets of
A090801, the distinct denominators of the Bernoulli numbers.
Conjecture (both entries): all first differences are multiples of 36.

Proof (Greathouse's comment in the entries): every Bernoulli denominator
other than 1 and 2 is the denominator of B_{2k}, k ≥ 1, and is ≡ 2 (mod 4)
(von Staudt–Clausen: 2 divides it, 4 does not; Mathlib `dvd_den_bernoulli`,
`not_sq_dvd_den_bernoulli`).  1 and 2 are ≡ 1, 2 (mod 9).  So the terms are
≡ 30 (mod 36) in A219543 and ≡ 6 (mod 36) in A218755, and any two terms
differ by a multiple of 36.

Main theorems: `A219543_main`, `A218755_main` (any two members of the set
differ by a multiple of 36; in particular consecutive terms).  The sets are
the entries' definitions with Mathlib's `bernoulli` (B₁ = -1/2; the
denominators do not depend on the sign convention).
-/
import Mathlib

/-- Denominators of B_{2k}, k ≥ 1, are ≡ 2 (mod 4). -/
theorem bernoulli_den_mod4 (k : ℕ) (hk : 0 < k) : (bernoulli (2 * k)).den % 4 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : 2 ∣ (bernoulli (2 * k)).den :=
    Bernoulli.dvd_den_bernoulli (p := 2) hk (by norm_num)
  have h2 : ¬ 2 ^ 2 ∣ (bernoulli (2 * k)).den :=
    Bernoulli.not_sq_dvd_den_bernoulli (p := 2) hk (by norm_num)
  omega

/-- Every Bernoulli denominator is 1, 2, or ≡ 2 (mod 4). -/
theorem bernoulli_den_cases (j : ℕ) :
    (bernoulli j).den = 1 ∨ (bernoulli j).den % 4 = 2 := by
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · left; subst h0; simp at hk; subst hk; simp
    · right; have : j = 2 * k := by omega
      subst this; exact bernoulli_den_mod4 k hpos
  · rcases Nat.lt_or_ge 1 j with hlt | hle
    · left; rw [bernoulli_eq_zero_of_odd hodd hlt]; rfl
    · right; have : j = 1 := by obtain ⟨t, ht⟩ := hodd; omega
      subst this; rw [bernoulli_one]; decide +kernel

/-- A219543 as a set: Bernoulli denominators ≡ 3 (mod 9). -/
def A219543set : Set ℕ := {d | ∃ j, (bernoulli j).den = d ∧ d % 9 = 3}

/-- A218755 as a set: Bernoulli denominators ≡ 6 (mod 9). -/
def A218755set : Set ℕ := {d | ∃ j, (bernoulli j).den = d ∧ d % 9 = 6}

theorem A219543_mod36 (d : ℕ) (hd : d ∈ A219543set) : d % 36 = 30 := by
  obtain ⟨j, rfl, h9⟩ := hd
  rcases bernoulli_den_cases j with h | h <;> omega

theorem A218755_mod36 (d : ℕ) (hd : d ∈ A218755set) : d % 36 = 6 := by
  obtain ⟨j, rfl, h9⟩ := hd
  rcases bernoulli_den_cases j with h | h <;> omega

theorem A219543_main (a b : ℕ) (ha : a ∈ A219543set) (hb : b ∈ A219543set) :
    (36 : ℤ) ∣ (b : ℤ) - a := by
  have := A219543_mod36 a ha
  have := A219543_mod36 b hb
  omega

theorem A218755_main (a b : ℕ) (ha : a ∈ A218755set) (hb : b ∈ A218755set) :
    (36 : ℤ) ∣ (b : ℤ) - a := by
  have := A218755_mod36 a ha
  have := A218755_mod36 b hb
  omega
