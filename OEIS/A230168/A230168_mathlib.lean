/-
OEIS A230168: primes of the form 45*2^n - 1.
Conjecture (entry comment): each term ends with digit 9.

Main theorem `A230168_main`: every prime p of the form 45*2^n - 1 (n : ℕ)
satisfies p % 10 = 9.  The case n = 0 gives 44, which is not prime; for
n ≥ 1, 45*2^n is a multiple of 10, so 45*2^n - 1 ≡ 9 (mod 10).

Checked here: the statement for the entry's definition (the set of primes of
that form).  Not checked: nothing else is claimed.
-/
import Mathlib

/-- Membership in A230168: p is prime and p = 45*2^n - 1 for some n. -/
def A230168 (p : ℕ) : Prop := p.Prime ∧ ∃ n : ℕ, p = 45 * 2 ^ n - 1

theorem A230168_digit (n : ℕ) (hn : 1 ≤ n) : (45 * 2 ^ n - 1) % 10 = 9 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : 45 * 2 ^ (m + 1) = 10 * (9 * 2 ^ m) := by ring
  have hp : 0 < 2 ^ m := by positivity
  rw [h]
  omega

theorem A230168_main (p : ℕ) (hp : A230168 p) : p % 10 = 9 := by
  obtain ⟨hpr, n, rfl⟩ := hp
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    exact absurd hpr (by norm_num)
  · exact A230168_digit n hpos
