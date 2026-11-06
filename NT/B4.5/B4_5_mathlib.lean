import Mathlib

/-
Guy, UPINT B4 (Hagis): an odd non-squarefree unitary amicable pair.
Witness: m = 581308455 = 3·5·7·13²·17·41·47, n = 603131865 = 3·5·7·17·71·4759.

Main theorem `odd_nonsquarefree_unitary_amicable`: with `usigma N` the sum of the divisors
d of N with gcd(d, N/d) = 1, usigma m = usigma n = m + n, m ≠ n, m and n are odd and m is
not squarefree. The two unitary sums are evaluated by the kernel from the definition
(`Nat.divisors_mul` splits the divisor set into those of small factors; `decide +kernel`).
Also checked: the factorizations, primality of the prime factors, and the formula
Π (1 + p^e) = m + n for both (`unitary_sums`).
-/

namespace NT_B4_5

theorem m_fact : (581308455 : ℕ) = 3 * 5 * 7 * 13 ^ 2 * 17 * 41 * 47 := by norm_num
theorem n_fact : (603131865 : ℕ) = 3 * 5 * 7 * 17 * 71 * 4759 := by norm_num

theorem primes : Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧
    Nat.Prime 41 ∧ Nat.Prime 47 ∧ Nat.Prime 71 ∧ Nat.Prime 4759 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem not_squarefree_m : ¬ Squarefree (581308455 : ℕ) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨13, by norm_num, by norm_num⟩

theorem odd_pair : Odd (581308455 : ℕ) ∧ Odd (603131865 : ℕ) := by
  constructor <;> decide

/-- σ*(m) and σ*(n) from the prime-power factorizations both equal m + n. -/
theorem unitary_sums :
    (1 + 3) * (1 + 5) * (1 + 7) * (1 + 13 ^ 2) * (1 + 17) * (1 + 41) * (1 + 47) =
      (581308455 + 603131865 : ℕ) ∧
    (1 + 3) * (1 + 5) * (1 + 7) * (1 + 17) * (1 + 71) * (1 + 4759) =
      (581308455 + 603131865 : ℕ) := by
  constructor <;> norm_num

/-- Unitary divisor sum: Σ of d | N with gcd(d, N/d) = 1. -/
def usigma (N : ℕ) : ℕ := ∑ d ∈ N.divisors.filter (fun d => Nat.Coprime d (N / d)), d

theorem usigma_m : usigma 581308455 = 581308455 + 603131865 := by
  unfold usigma
  rw [show (581308455 : ℕ) = 3 * 5 * 7 * 169 * 17 * 41 * 47 by norm_num]
  simp only [Nat.divisors_mul]
  decide +kernel


theorem usigma_n : usigma 603131865 = 581308455 + 603131865 := by
  unfold usigma
  rw [show (603131865 : ℕ) = 3 * 5 * 7 * 17 * 71 * 4759 by norm_num]
  simp only [Nat.divisors_mul]
  decide +kernel

/-- (581308455, 603131865) is an odd unitary amicable pair whose smaller member is not squarefree. -/
theorem odd_nonsquarefree_unitary_amicable :
    usigma 581308455 = 581308455 + 603131865 ∧ usigma 603131865 = 581308455 + 603131865 ∧
    (581308455 : ℕ) ≠ 603131865 ∧ Odd (581308455 : ℕ) ∧ Odd (603131865 : ℕ) ∧
    ¬ Squarefree (581308455 : ℕ) :=
  ⟨usigma_m, usigma_n, by norm_num, odd_pair.1, odd_pair.2, not_squarefree_m⟩
