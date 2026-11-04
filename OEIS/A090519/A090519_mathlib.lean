/-
OEIS A090519 (smallest prime p with floor(10^n/p) prime, 0 if none),
conjecture: no term is zero.

Main theorem `A090519_conjecture`: for every n ≥ 1 there is a prime p with
10^n / p (natural-number floor division) prime.  This is the README result.
Proof: n = 1 uses p = 2.  For n ≥ 2, 10^n = 4m and Bertrand's postulate
(Mathlib `Nat.exists_prime_lt_and_le_two_mul`) gives a prime m < p ≤ 2m, so
10^n / p ∈ {2, 3}.

Not checked: nothing outside Lean.
-/
import Mathlib

theorem A090519_conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ (10 ^ n / p).Prime := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    exact ⟨2, Nat.prime_two, by norm_num⟩
  · obtain ⟨m, hm⟩ : ∃ m, 10 ^ n = 4 * m := by
      refine ⟨25 * 10 ^ (n - 2), ?_⟩
      have : 10 ^ n = 10 ^ 2 * 10 ^ (n - 2) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0] at hm; exact absurd hm (by positivity)
    obtain ⟨p, hp, hmp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul m hm0
    refine ⟨p, hp, ?_⟩
    have hp0 : 0 < p := hp.pos
    have hlt : 10 ^ n / p < 4 := by
      rw [Nat.div_lt_iff_lt_mul hp0]; omega
    have hge : 2 ≤ 10 ^ n / p := by
      rw [Nat.le_div_iff_mul_le hp0]; omega
    have : 10 ^ n / p = 2 ∨ 10 ^ n / p = 3 := by omega
    rcases this with h' | h' <;> rw [h'] <;> norm_num
