import Mathlib

/-
OEIS A126142 (Mathlib): primes p whose square has a prime decimal digit sum. Comment
(V. Librandi, 2009): "a(n)^2 is of the form 6*k+1". README result: true (trivial).

Main theorem `A126142_main`: every prime p such that `(Nat.digits 10 (p ^ 2)).sum` is prime
satisfies p^2 = 6k + 1 for some k. This is the comment for every term of the sequence.

Proof. p = 2 and p = 3 are not terms (digit sums 4 and 9 are not prime), so p ≥ 5 is prime,
hence odd and not divisible by 3, and p^2 ≡ 1 (mod 24) by a check of the residues mod 24
(as in the core file A126142.lean).

Outside Lean: nothing.
-/

theorem A126142_residues : ∀ r, r < 24 → r % 2 = 1 → r % 3 ≠ 0 → r ^ 2 % 24 = 1 := by decide

theorem A126142_sq_mod_24 (n : ℕ) (h2 : n % 2 = 1) (h3 : n % 3 ≠ 0) : n ^ 2 % 24 = 1 := by
  rw [Nat.pow_mod]
  exact A126142_residues (n % 24) (Nat.mod_lt _ (by decide)) (by omega) (by omega)

theorem A126142_main (p : ℕ) (hp : p.Prime) (hs : (Nat.digits 10 (p ^ 2)).sum.Prime) :
    ∃ k, p ^ 2 = 6 * k + 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hs
  have hp3 : p ≠ 3 := by
    rintro rfl
    norm_num at hs
  have h2 : p % 2 = 1 := by
    by_contra h0
    rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)) with h | h <;> omega
  have h3 : p % 3 ≠ 0 := by
    intro h0
    rcases hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
  have := A126142_sq_mod_24 p h2 h3
  exact ⟨p ^ 2 / 6, by omega⟩
