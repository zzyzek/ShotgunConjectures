/-
OEIS A065129: a(n) = least m with m / A003285(m) = n (A003285(m) = period of the
continued fraction of sqrt m). Conjecture: A003285(m) is even or in A004613
(all prime factors = 1 mod 4) whenever A003285(m) divides m; editorial reading:
every odd term of A065129 is in A004613.

Checked here: if x^2 + 1 = m y^2 (negative Pell equation solvable) then every odd
prime factor of m is 1 mod 4 (`prime_dvd_of_negPell`); hence an odd divisor l of
such m has all prime factors 1 mod 4 (`odd_divisor_A004613`), and so does m itself
when m is odd (`odd_m_A004613`).
Not checked here: the classical fact that an odd period of sqrt m gives a solution
of x^2 - m y^2 = -1 (Legendre; the last convergent before the end of the first
period). certificate/check.py tests the whole statement for m < 300000.
-/
import Mathlib

theorem prime_dvd_of_negPell {m x y : ℕ} (h : x ^ 2 + 1 = m * y ^ 2) {p : ℕ} (hp : p.Prime)
    (hpm : p ∣ m) (hp2 : p ≠ 2) : p % 4 = 1 := by
  have := Fact.mk hp
  have hm : (m : ZMod p) = 0 := by
    obtain ⟨k, rfl⟩ := hpm
    push_cast
    simp
  have hc : ((x : ZMod p)) ^ 2 + 1 = 0 := by
    have := congrArg (fun n : ℕ => (n : ZMod p)) h
    push_cast at this
    rw [this, hm, zero_mul]
  have hsq : IsSquare (-1 : ZMod p) := ⟨(x : ZMod p), by linear_combination -hc⟩
  have h3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h hp2
  · omega

theorem odd_divisor_A004613 {m x y l : ℕ} (h : x ^ 2 + 1 = m * y ^ 2) (hl : l ∣ m)
    (hlodd : l % 2 = 1) : ∀ p, p.Prime → p ∣ l → p % 4 = 1 := by
  intro p hp hpl
  apply prime_dvd_of_negPell h hp (dvd_trans hpl hl)
  rintro rfl
  omega

theorem odd_m_A004613 {m x y : ℕ} (h : x ^ 2 + 1 = m * y ^ 2) (hmodd : m % 2 = 1) :
    ∀ p, p.Prime → p ∣ m → p % 4 = 1 :=
  odd_divisor_A004613 h dvd_rfl hmodd
