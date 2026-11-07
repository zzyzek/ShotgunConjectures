/-
OEIS A219543 (and A218755): denominators of Bernoulli numbers that are
≡ 3 (mod 9) (A219543), resp. ≡ 6 (mod 9) (A218755); both are subsets of
A090801, the distinct denominators of the Bernoulli numbers.
Conjecture (both entries): all first differences are multiples of 36.

Proof (Greathouse's comment in the entries): every Bernoulli denominator
other than 1 and 2 is the denominator of B_{2k}, k ≥ 1, and is ≡ 2 (mod 4)
(von Staudt–Clausen: 2 divides it, 4 does not; Mathlib `dvd_den_bernoulli`,
`not_sq_dvd_den_bernoulli`; library
`OpenProblemsLib.BernoulliDen.bernoulli_den_mod4`, `bernoulli_den_cases`).
1 and 2 are ≡ 1, 2 (mod 9).  So the terms are ≡ 30 (mod 36) in A219543 and
≡ 6 (mod 36) in A218755, and any two terms differ by a multiple of 36.

Main theorems: `A219543_main`, `A218755_main` (any two members of the set
differ by a multiple of 36; in particular consecutive terms).  The sets are
the entries' definitions with Mathlib's `bernoulli` (B₁ = -1/2; the
denominators do not depend on the sign convention).
-/
import Mathlib
import OpenProblemsLib.BernoulliDen

open OpenProblemsLib.BernoulliDen

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
