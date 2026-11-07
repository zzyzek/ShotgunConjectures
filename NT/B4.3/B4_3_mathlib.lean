import Mathlib
import OpenProblemsLib.Pratt

/-
Guy, UPINT B4: is te Riele's 33-digit odd amicable pair coprime to 3 the smallest such pair?
No: the 32-digit pair
  m = 42262694537514864075544955198125 = 5^4·7^2·11^2·13^2·19^3·29·37·71·109·181·347·2833·6659,
  n = 42405817271188606697466971841875 = 5^4·7^2·11^2·13^2·19^3·29·37·71·109·181·6568305119
(listed by Pedersen; quoted by MathWorld) is amicable, odd and coprime to 3.

Checked here: σ₁ m = σ₁ n = m + n with σ₁ = Mathlib's `ArithmeticFunction.sigma 1` (sum of
divisors), m ≠ n, both odd, neither divisible by 3, m < 10^32 (so m has at most 32 digits).
Primality of every prime factor (6568305119 by a Pratt certificate, the others by norm_num),
multiplicativity of σ₁ from Mathlib. Not checked: the digit count of te Riele's pair (Guy's
text), and whether a still smaller odd pair coprime to 3 exists (open).
-/

namespace NT_B4_3

open ArithmeticFunction OpenProblemsLib
open scoped ArithmeticFunction.sigma

theorem prime_big : Nat.Prime 6568305119 :=
  prime_of_prattCertifies _ [⟨2, 1, []⟩,
  ⟨5, 2, [(2, 2)]⟩,
  ⟨11, 2, [(2, 1), (5, 1)]⟩,
  ⟨89, 3, [(2, 3), (11, 1)]⟩,
  ⟨179, 2, [(2, 1), (89, 1)]⟩,
  ⟨3, 2, [(2, 1)]⟩,
  ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
  ⟨17, 3, [(2, 4)]⟩,
  ⟨137, 3, [(2, 3), (17, 1)]⟩,
  ⟨101929, 17, [(2, 3), (3, 1), (31, 1), (137, 1)]⟩,
  ⟨18347221, 2, [(2, 2), (3, 2), (5, 1), (101929, 1)]⟩,
  ⟨6568305119, 17, [(2, 1), (179, 1), (18347221, 1)]⟩] (by decide +kernel)

theorem smul {a b : ℕ} (h : Nat.Coprime a b) : σ 1 (a * b) = σ 1 a * σ 1 b :=
  isMultiplicative_sigma.map_mul_of_coprime h

theorem spp {p i : ℕ} (hp : p.Prime) : σ 1 (p ^ i) = ∑ k ∈ Finset.range (i + 1), p ^ k :=
  sigma_one_apply_prime_pow hp

/-- σ₁ of the common part A = 5^4·7^2·11^2·13^2·19^3·29·37·71·109·181. -/
theorem sigma_A :
    σ 1 (5^4 * (7^2 * (11^2 * (13^2 * (19^3 * (29^1 * (37^1 * (71^1 * (109^1 * 181^1))))))))) =
      (∑ k ∈ Finset.range 5, 5 ^ k) * ((∑ k ∈ Finset.range 3, 7 ^ k) *
      ((∑ k ∈ Finset.range 3, 11 ^ k) * ((∑ k ∈ Finset.range 3, 13 ^ k) *
      ((∑ k ∈ Finset.range 4, 19 ^ k) * ((∑ k ∈ Finset.range 2, 29 ^ k) *
      ((∑ k ∈ Finset.range 2, 37 ^ k) * ((∑ k ∈ Finset.range 2, 71 ^ k) *
      ((∑ k ∈ Finset.range 2, 109 ^ k) * (∑ k ∈ Finset.range 2, 181 ^ k))))))))) := by
  rw [smul (by norm_num), smul (by norm_num), smul (by norm_num), smul (by norm_num),
    smul (by norm_num), smul (by norm_num), smul (by norm_num), smul (by norm_num),
    smul (by norm_num)]
  rw [spp (by norm_num), spp (by norm_num), spp (by norm_num), spp (by norm_num),
    spp (by norm_num), spp (by norm_num), spp (by norm_num), spp (by norm_num),
    spp (by norm_num), spp (by norm_num)]

def A : ℕ := 5^4 * (7^2 * (11^2 * (13^2 * (19^3 * (29^1 * (37^1 * (71^1 * (109^1 * 181^1))))))))

theorem sigma_A' : σ 1 A = 12890465692724011392000 := by
  unfold A; rw [sigma_A]; simp [Finset.sum_range_succ]

theorem sigma_p {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := spp (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using this

theorem m_eq : (42262694537514864075544955198125 : ℕ) = A * (347 * (2833 * 6659)) := by
  unfold A; norm_num

theorem n_eq : (42405817271188606697466971841875 : ℕ) = A * 6568305119 := by
  unfold A; norm_num

theorem sigma_m : σ 1 42262694537514864075544955198125 =
    42262694537514864075544955198125 + 42405817271188606697466971841875 := by
  rw [m_eq, smul (by unfold A; norm_num), smul (by norm_num), smul (by norm_num),
    sigma_A', sigma_p (by norm_num), sigma_p (by norm_num), sigma_p (by norm_num)]
  unfold A; norm_num

theorem sigma_n : σ 1 42405817271188606697466971841875 =
    42262694537514864075544955198125 + 42405817271188606697466971841875 := by
  rw [n_eq, smul (by unfold A; norm_num), sigma_A', sigma_p prime_big]
  unfold A; norm_num

/-- An odd amicable pair coprime to 3 whose members are below 10^32 (32 digits). -/
theorem odd_amicable_coprime3_32digits :
    σ 1 42262694537514864075544955198125 =
      42262694537514864075544955198125 + 42405817271188606697466971841875 ∧
    σ 1 42405817271188606697466971841875 =
      42262694537514864075544955198125 + 42405817271188606697466971841875 ∧
    (42262694537514864075544955198125 : ℕ) ≠ 42405817271188606697466971841875 ∧
    Odd (42262694537514864075544955198125 : ℕ) ∧ Odd (42405817271188606697466971841875 : ℕ) ∧
    ¬ 3 ∣ (42262694537514864075544955198125 : ℕ) ∧ ¬ 3 ∣ (42405817271188606697466971841875 : ℕ) ∧
    (42262694537514864075544955198125 : ℕ) < 10 ^ 32 ∧
    (42405817271188606697466971841875 : ℕ) < 10 ^ 32 := by
  refine ⟨sigma_m, sigma_n, by norm_num, by decide, by decide, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

