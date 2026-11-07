import Mathlib

/-
OEIS A065255.  b(k) = k-th number n whose last decimal digit equals that of sigma(n),
i.e. sigma(n) ≡ n (mod 10).  Conjecture (B. Cloitre, 2002): b(k)/k → 10.

Checked here: the arithmetic core.
* `A065255_ten_dvd_sigma`: if a prime p ≡ 9 (mod 10) divides n exactly once, then
  10 ∣ sigma(n).
* `A065255_iff`: under the same hypothesis, sigma(n) ≡ n (mod 10) iff 10 ∣ n.

Not checked here: the density step (almost every n has a prime p ≡ 9 mod 10 dividing it
exactly once, by divergence of the sum of 1/p over such primes), written out in README.md.
-/

open ArithmeticFunction

theorem A065255_ten_dvd_sigma (n p : ℕ) (hp : p.Prime) (h9 : p % 10 = 9)
    (hdvd : p ∣ n) (hnd : ¬ p ^ 2 ∣ n) : 10 ∣ sigma 1 n := by
  obtain ⟨m, rfl⟩ := hdvd
  have hm : ¬ p ∣ m := by
    intro h
    obtain ⟨c, rfl⟩ := h
    exact hnd ⟨c, by ring⟩
  have hcop : Nat.Coprime p m := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  have hs : sigma 1 p = p + 1 := by
    have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
    rw [pow_one] at this
    rw [this]
    simp [Finset.sum_range_succ]
    ring
  rw [hs]
  exact Dvd.dvd.mul_right (by omega) _

theorem A065255_iff (n p : ℕ) (hp : p.Prime) (h9 : p % 10 = 9)
    (hdvd : p ∣ n) (hnd : ¬ p ^ 2 ∣ n) : sigma 1 n % 10 = n % 10 ↔ n % 10 = 0 := by
  have h := A065255_ten_dvd_sigma n p hp h9 hdvd hnd
  omega
