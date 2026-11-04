/-
OEIS A098016, Mathlib proof.

Conjecture (OEIS A098016): (1/2)(prime(x+1) + prime(x)) is not prime for
any x.

Main theorem `A098016_main`: for every index x and every prime q,
2·q ≠ p_x + p_{x+1}, where p_x = `Nat.nth Nat.Prime x` is the x-th prime
(0-indexed, p_0 = 2). So the mean of two consecutive primes is never a
prime. This is the README result for all x (the OEIS index is x + 1).

Proof: for x = 0 the sum 2 + 3 is odd; otherwise the mean lies strictly
between consecutive primes. Nothing is outside Lean.
-/
import Mathlib

theorem A098016_main (x q : ℕ) (hq : q.Prime) :
    2 * q ≠ Nat.nth Nat.Prime x + Nat.nth Nat.Prime (x + 1) := by
  intro h
  have hlt : Nat.nth Nat.Prime x < Nat.nth Nat.Prime (x + 1) :=
    (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).2 (Nat.lt_succ_self x)
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three] at h
    omega
  · have h2 : 2 < Nat.nth Nat.Prime x := by
      have := (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).2 hx
      rwa [Nat.nth_prime_zero_eq_two] at this
    have hp1 : (Nat.nth Nat.Prime x).Prime := Nat.prime_nth_prime x
    have hodd : Odd (Nat.nth Nat.Prime x) := hp1.odd_of_ne_two (by omega)
    have hp2 : (Nat.nth Nat.Prime (x + 1)).Prime := Nat.prime_nth_prime (x + 1)
    have hodd2 : Odd (Nat.nth Nat.Prime (x + 1)) := hp2.odd_of_ne_two (by omega)
    obtain ⟨a, ha⟩ := hodd
    obtain ⟨b, hb⟩ := hodd2
    have hq1 : Nat.nth Nat.Prime x < q := by omega
    have hq2 : q < Nat.nth Nat.Prime (x + 1) := by omega
    have := Nat.le_nth_of_lt_nth_succ hq2 hq
    omega
