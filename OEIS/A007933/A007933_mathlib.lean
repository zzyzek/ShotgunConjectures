import Mathlib

/-
OEIS A007933: numbers n such that some permutation of the digits of n is a prime
(leading zeros allowed: 20 is a term because 02 = 2).  Conjecture (C. R. Greathouse IV,
2012): a(n) ~ 3n/2, i.e. the set has density 2/3.  The same conjecture is stated for
A007934 (some nontrivial permutation) and A007935 (composite terms of A007933).

Checked here: the upper half of the density statement in its arithmetic form.
* `A007933_mod_three_perm`: every arrangement of the digits of n is congruent to n mod 3.
* `A007933_three_dvd`: if 3 ∣ n and n is a term, then some arrangement of its digits
  equals 3.  So every term is either coprime to 3 or has one digit 3 and all other digits 0.

Not checked here: the counting step (numbers ≤ x with digits {3, 0, ..., 0} number at most
log10 x + 1, so #terms ≤ x is at most ⌈2x/3⌉ + log10 x + 1), and the conjectured lower bound.
-/



/-- `n` is a term: some list that is a permutation of the base-10 digits of `n`
(little-endian, so permuted zeros may become leading zeros) reads as a prime. -/
def A007933IsTerm (n : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (Nat.digits 10 n) ∧ (Nat.ofDigits 10 l).Prime

theorem A007933_ofDigits_mod_three (l : List ℕ) : Nat.ofDigits 10 l ≡ l.sum [MOD 3] := by
  have h := Nat.ofDigits_modEq 10 3 l
  simpa [Nat.ofDigits_one] using h

theorem A007933_mod_three_perm (n : ℕ) (l : List ℕ) (hl : l.Perm (Nat.digits 10 n)) :
    Nat.ofDigits 10 l ≡ n [MOD 3] := by
  have h1 := A007933_ofDigits_mod_three l
  have h2 := A007933_ofDigits_mod_three (Nat.digits 10 n)
  rw [Nat.ofDigits_digits] at h2
  rw [hl.sum_eq] at h1
  exact h1.trans h2.symm

theorem A007933_three_dvd (n : ℕ) (h3 : 3 ∣ n) (hn : A007933IsTerm n) :
    ∃ l : List ℕ, l.Perm (Nat.digits 10 n) ∧ Nat.ofDigits 10 l = 3 := by
  obtain ⟨l, hl, hp⟩ := hn
  refine ⟨l, hl, ?_⟩
  have hm := A007933_mod_three_perm n l hl
  have hd : 3 ∣ Nat.ofDigits 10 l :=
    (Nat.modEq_zero_iff_dvd.mp (hm.trans (Nat.modEq_zero_iff_dvd.mpr h3)))
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd).symm


