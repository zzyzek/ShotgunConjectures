import Mathlib

/-!
# Denominators of Bernoulli numbers (von Staudt-Clausen)

Consequences of Mathlib's von Staudt-Clausen theorem (`Bernoulli.vonStaudt_clausen`,
`Bernoulli.dvd_den_bernoulli`, `Bernoulli.not_sq_dvd_den_bernoulli`) for the denominators of
`bernoulli n` (Mathlib convention `B₁ = -1/2`; denominators do not depend on the sign of `B₁`).

Definitions.
* `vscSet k` : the primes `p` with `(p - 1) ∣ 2k` (as a filter of `range (2k + 2)`).

Main results.
* `bernoulli_den_dvd_prod` : `den B_{2k} ∣ ∏_{p ∈ vscSet k} p` for every `k`.
* `bernoulli_den_eq_prod` : `den B_{2k} = ∏_{p ∈ vscSet k} p` for `k ≥ 1`.
* `bernoulli_den_not_dvd` : a prime `p` with `¬ (p - 1) ∣ 2k` does not divide `den B_{2k}`.
* `bernoulli_den_mod4` : `den B_{2k} ≡ 2 (mod 4)` for `k ≥ 1`.
* `bernoulli_den_cases` : every `den B_j` is `1` or `≡ 2 (mod 4)`.

Used by OEIS A219196, A219543, A141459.
-/

namespace OpenProblemsLib.BernoulliDen

open Finset

/-- The primes in the von Staudt-Clausen sum for `B_{2k}`: primes `p` with `(p - 1) ∣ 2k`. -/
def vscSet (k : ℕ) : Finset ℕ :=
  (range (2 * k + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * k)

/-- The denominator of `B_{2k}` divides the product of the primes `p` with `(p - 1) ∣ 2k`. -/
theorem bernoulli_den_dvd_prod (k : ℕ) : (bernoulli (2 * k)).den ∣ ∏ p ∈ vscSet k, p := by
  obtain ⟨N, hN⟩ := Bernoulli.vonStaudt_clausen k
  set P : ℕ := ∏ p ∈ vscSet k, p with hP
  have hPpos : P ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    intro p hp
    exact (Finset.mem_filter.1 hp).2.1.ne_zero
  have hsum : (P : ℚ) * ∑ p ∈ vscSet k, (1 : ℚ) / p
      = ((∑ p ∈ vscSet k, P / p : ℕ) : ℚ) := by
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hpp := (Finset.mem_filter.1 hp).2.1
    have hdvd : p ∣ P := Finset.dvd_prod_of_mem _ hp
    rw [Nat.cast_div hdvd (by exact_mod_cast hpp.ne_zero)]
    ring
  set M : ℕ := ∑ p ∈ vscSet k, P / p with hM
  clear_value M
  have hint : (P : ℚ) * bernoulli (2 * k) = (((P : ℤ) * N - (M : ℤ) : ℤ) : ℚ) := by
    have : bernoulli (2 * k) = (N : ℚ) - ∑ p ∈ vscSet k, (1 : ℚ) / p := by
      rw [hN]; unfold vscSet; ring
    rw [this, mul_sub, hsum]
    push_cast
    ring
  have hB : bernoulli (2 * k) = ((P : ℚ) * bernoulli (2 * k)) * (P : ℚ)⁻¹ := by
    field_simp
  have hd := Rat.mul_den_dvd ((P : ℚ) * bernoulli (2 * k)) ((P : ℚ)⁻¹)
  rw [← hB, hint, Rat.den_intCast, one_mul,
    show ((P : ℚ)⁻¹).den = P by simp [hPpos]] at hd
  exact hd

/-- von Staudt-Clausen: for `k ≥ 1`, `den B_{2k}` is the product of the primes `p` with
`(p - 1) ∣ 2k`. -/
theorem bernoulli_den_eq_prod (k : ℕ) (hk : 0 < k) :
    (bernoulli (2 * k)).den = ∏ p ∈ vscSet k, p := by
  apply Nat.dvd_antisymm (bernoulli_den_dvd_prod k)
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Finset.mem_filter.1 hp).2.1.prime
  · intro p hp
    have h := Finset.mem_filter.1 hp
    have : Fact p.Prime := ⟨h.2.1⟩
    exact Bernoulli.dvd_den_bernoulli hk h.2.2

/-- A prime `p` with `¬ (p - 1) ∣ 2k` does not divide `den B_{2k}` (any `k`). -/
theorem bernoulli_den_not_dvd (k p : ℕ) [hp : Fact p.Prime] (hpk : ¬ (p - 1) ∣ 2 * k) :
    ¬ p ∣ (bernoulli (2 * k)).den := by
  intro h
  obtain ⟨q, hq, hpq⟩ :=
    (Prime.dvd_finsetProd_iff hp.out.prime _).mp (h.trans (bernoulli_den_dvd_prod k))
  have hqp := (Finset.mem_filter.mp hq).2
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp.out hqp.1).mp hpq
  exact hpk (this ▸ hqp.2)

/-- Denominators of `B_{2k}`, `k ≥ 1`, are `≡ 2 (mod 4)`. -/
theorem bernoulli_den_mod4 (k : ℕ) (hk : 0 < k) : (bernoulli (2 * k)).den % 4 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : 2 ∣ (bernoulli (2 * k)).den :=
    Bernoulli.dvd_den_bernoulli (p := 2) hk (by norm_num)
  have h2 : ¬ 2 ^ 2 ∣ (bernoulli (2 * k)).den :=
    Bernoulli.not_sq_dvd_den_bernoulli (p := 2) hk (by norm_num)
  omega

/-- Every Bernoulli denominator is `1` or `≡ 2 (mod 4)`. -/
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

end OpenProblemsLib.BernoulliDen
