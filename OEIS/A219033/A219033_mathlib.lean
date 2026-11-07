import Mathlib

/-!
# OEIS A219033: the sequence is infinite; the "6*A185208(n), ratio 214/3" conjecture fails at 107

A219033: numbers k = x + y (x, y >= 1) with sigma_1(k) = sigma_1(x) + sigma_1(y) and
sigma_2(k) = sigma_2(x) + sigma_2(y).

Checked here.
* `A219033_family` : if `gcd(m, 278628) = 1` (278628 = 4*3*7*31*107) then `434 m` is a term, with
  `x = 428 m`, `y = 6 m`.
* `A219033_infinite` : the set of terms is infinite (Perry's first conjecture).
* `A219033_ratio_fails` : `107` lies in A185208 (no divisor `d > 1` with `d + 1` a prime power), but
  `x = 6*107`, `y = (214/3) x = 428*107` violates the sigma_1 equality (Perry's fifth conjecture is false).
Not checked here: the conjectures that all terms and parts are even and that no term satisfies the
sigma_3 equality (open; certificate/family.py checks them for k <= 16100 only).
-/

namespace A219033

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `k` is a term of A219033. -/
def InSeq (k : ℕ) : Prop :=
  ∃ x y, 0 < x ∧ 0 < y ∧ k = x + y ∧ σ 1 k = σ 1 x + σ 1 y ∧ σ 2 k = σ 2 x + σ 2 y

/-- Membership in A185208: no divisor `d > 1` with `d + 1` a prime power. -/
def InA185208 (m : ℕ) : Prop := 0 < m ∧ ∀ d, d ∣ m → 1 < d → ¬ IsPrimePow (d + 1)

theorem sigma_mul {a b : ℕ} (k : ℕ) (h : Nat.Coprime a b) : σ k (a * b) = σ k a * σ k b :=
  isMultiplicative_sigma.map_mul_of_coprime h

theorem A219033_family (m : ℕ) (hm : 0 < m) (h : Nat.Coprime 278628 m) : InSeq (434 * m) := by
  have c434 : Nat.Coprime 434 m := Nat.Coprime.coprime_dvd_left (by norm_num) h
  have c428 : Nat.Coprime 428 m := Nat.Coprime.coprime_dvd_left (by norm_num) h
  have c6 : Nat.Coprime 6 m := Nat.Coprime.coprime_dvd_left (by norm_num) h
  refine ⟨428 * m, 6 * m, by omega, by omega, by ring, ?_, ?_⟩
  · rw [sigma_mul 1 c434, sigma_mul 1 c428, sigma_mul 1 c6]
    have e1 : σ 1 434 = 768 := by decide
    have e2 : σ 1 428 = 756 := by decide
    have e3 : σ 1 6 = 12 := by decide
    rw [e1, e2, e3]; ring
  · rw [sigma_mul 2 c434, sigma_mul 2 c428, sigma_mul 2 c6]
    have e1 : σ 2 434 = 240500 := by decide
    have e2 : σ 2 428 = 240450 := by decide
    have e3 : σ 2 6 = 50 := by decide
    rw [e1, e2, e3]; ring

theorem coprime_step (t : ℕ) : Nat.Coprime 278628 (278628 * t + 1) := by
  rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_comm, Nat.gcd_mul_left_add_right]
  exact Nat.gcd_one_right _

theorem A219033_infinite : {k | InSeq k}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => 434 * (278628 * t + 1))
  · intro a b hab
    simp only at hab
    omega
  · intro t
    exact A219033_family _ (by omega) (coprime_step t)

theorem not_isPrimePow_108 : ¬ IsPrimePow 108 := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, hpk⟩
  have h2 : 2 ∣ p ^ k := by rw [hpk]; norm_num
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have h3 : 3 ∣ p ^ k := by rw [hpk]; norm_num
  rw [hp2] at h3
  have := Nat.prime_three.dvd_of_dvd_pow h3
  omega

theorem in_A185208_107 : InA185208 107 := by
  refine ⟨by norm_num, fun d hd h1 => ?_⟩
  have hp : Nat.Prime 107 := by norm_num
  rcases hp.eq_one_or_self_of_dvd d hd with rfl | rfl
  · omega
  · exact not_isPrimePow_108

/-- Perry's conjecture "lower part 6*A185208(n), upper part 214/3 of it satisfies the equalities"
fails at `A185208` member `107`: `sigma_1(434*107) ≠ sigma_1(428*107) + sigma_1(6*107)`. -/
theorem A219033_ratio_fails :
    InA185208 107 ∧ σ 1 (434 * 107) ≠ σ 1 (428 * 107) + σ 1 (6 * 107) := by
  refine ⟨in_A185208_107, ?_⟩
  have a : σ 1 (434 * 107) = σ 1 434 * σ 1 107 := sigma_mul 1 (by norm_num)
  have b : σ 1 (428 * 107) = σ 1 4 * σ 1 11449 := by
    rw [show 428 * 107 = 4 * 11449 by norm_num]; exact sigma_mul 1 (by norm_num)
  have c : σ 1 (6 * 107) = σ 1 6 * σ 1 107 := sigma_mul 1 (by norm_num)
  have v1 : σ 1 434 = 768 := by decide
  have v2 : σ 1 107 = 108 := by decide
  have v3 : σ 1 4 = 7 := by decide
  have v4 : σ 1 11449 = 11557 := by
    rw [show (11449 : ℕ) = 107 ^ 2 by norm_num, sigma_apply_prime_pow (by norm_num)]
    simp [Finset.sum_range_succ]
  have v5 : σ 1 6 = 12 := by decide
  rw [a, b, c, v1, v2, v3, v4, v5]
  norm_num
