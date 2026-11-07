/-
OEIS A215926: a(n) = smallest deficient k such that k*n is perfect or
abundant.  Conjectures (entry): (1) a(n) is 1, 3 or a power of 2; (2) the
first occurrence of 2^m is at A014210(m) = nextprime(2^m).

Checked here (`A215926_at_prime`): for m ≥ 0 and every prime p with
2^m < p < 2^(m+1), either a(p) = 2^m, or a(p) = k is an almost perfect
number (σ(k) = 2k - 1) that is not a power of 2, with p + 1 ≤ 2k and k < 2^m.
Bertrand's postulate puts nextprime(2^m) in that range.  So a(A014210(m)) = 2^m
unless such an almost perfect number exists, and then both conjectures fail
at n = A014210(m).

Not checked here: that a(n) ≠ 2^m for 2 ≤ n < nextprime(2^m) (hand proof in
README, via a(n) ≤ max(3, 2^(m-1)) there), and the computer search showing no
almost perfect numbers other than powers of 2 up to 2·10^7.

Definitions follow google-deepmind/formal-conjectures OeisA215926.
-/
import Mathlib

open ArithmeticFunction

/-- Smallest deficient k with k*n perfect or abundant. -/
noncomputable def A215926 (n : ℕ) : ℕ :=
  sInf {k : ℕ | k.Deficient ∧ ((k * n).Perfect ∨ (k * n).Abundant)}

theorem sum_div_eq (n : ℕ) : ∑ i ∈ n.divisors, i = (∑ i ∈ n.properDivisors, i) + n :=
  Nat.sum_divisors_eq_sum_properDivisors_add_self

theorem deficient_iff' (n : ℕ) : n.Deficient ↔ ∑ i ∈ n.divisors, i < 2 * n := by
  unfold Nat.Deficient; rw [sum_div_eq]; omega

theorem nondef_iff (n : ℕ) (hn : 0 < n) :
    (n.Perfect ∨ n.Abundant) ↔ 2 * n ≤ ∑ i ∈ n.divisors, i := by
  unfold Nat.Perfect Nat.Abundant; rw [sum_div_eq]; omega

theorem sigma_mul_prime (k p : ℕ) (hp : p.Prime) (hk : ¬ p ∣ k) :
    ∑ i ∈ (k * p).divisors, i = (∑ i ∈ k.divisors, i) * (p + 1) := by
  have hc : k.Coprime p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hk))
  rw [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hc, sigma_one_apply,
    sigma_one_apply]
  congr 1
  have := sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one] at this
  rw [← sigma_one_apply, this]
  simp [Finset.sum_range_succ]; ring

theorem sigma_two_pow (j : ℕ) : ∑ i ∈ (2 ^ j).divisors, i + 1 = 2 ^ (j + 1) := by
  rw [← sigma_one_apply, sigma_one_apply_prime_pow Nat.prime_two]
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, add_right_comm, ih, pow_succ, pow_succ]; ring

theorem A215926_at_prime (m p : ℕ) (hp : p.Prime) (h1 : 2 ^ m < p)
    (h2 : p < 2 ^ (m + 1)) :
    A215926 p = 2 ^ m ∨
      (∑ i ∈ (A215926 p).divisors, i + 1 = 2 * A215926 p ∧
        (∀ j, A215926 p ≠ 2 ^ j) ∧ p + 1 ≤ 2 * A215926 p ∧ A215926 p < 2 ^ m) := by
  set T := {k : ℕ | k.Deficient ∧ ((k * p).Perfect ∨ (k * p).Abundant)} with hT
  have hpos : 0 < 2 ^ m := by positivity
  have hpk : ¬ p ∣ 2 ^ m := fun h => by have := Nat.le_of_dvd hpos h; omega
  have hmem : 2 ^ m ∈ T := by
    refine ⟨Nat.prime_two.deficient_pow, ?_⟩
    rw [nondef_iff _ (Nat.mul_pos hpos hp.pos), sigma_mul_prime _ _ hp hpk]
    have hs := sigma_two_pow m
    have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    nlinarith
  have hle : A215926 p ≤ 2 ^ m := Nat.sInf_le hmem
  have hin : A215926 p ∈ T := Nat.sInf_mem ⟨_, hmem⟩
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact Or.inl heq
  · right
    set k := A215926 p with hk
    obtain ⟨hdef, hnd⟩ := hin
    have kpos : 0 < k := hdef.pos
    have hpk' : ¬ p ∣ k := fun h => by have := Nat.le_of_dvd kpos h; omega
    rw [nondef_iff _ (Nat.mul_pos kpos hp.pos), sigma_mul_prime _ _ hp hpk'] at hnd
    rw [deficient_iff'] at hdef
    set s := ∑ i ∈ k.divisors, i with hs
    have hkp : k < p := by omega
    have hs1 : s + 1 = 2 * k := by
      by_contra hne
      have : s + 2 ≤ 2 * k := by omega
      nlinarith
    refine ⟨hs1, ?_, ?_, hlt⟩
    · intro j hj
      have hjm : j < m := by
        by_contra hc
        have : 2 ^ m ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hsj := sigma_two_pow j
      rw [← hj] at hsj
      have : 2 ^ (j + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    · nlinarith
