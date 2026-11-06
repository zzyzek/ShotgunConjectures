/-
OEIS A196226: m such that sigma(m) mod m = 3 + m/2. Layman's conjectures: for terms m >= 14,
sigma_2(m) = 5 + m/2 (mod m); for m >= 22, sigma_3(m) = 9 + m/2; for m >= 38,
sigma_4(m) = 17 + m/2 (mod m).

Checked here: m = 690 = 2*3*5*23 is a term (sigma(690) mod 690 = 348 = 3 + 345), and it violates
all three conjectures: sigma_2(690) mod 690 = 380 (not 350), sigma_3(690) mod 690 = 426 (not 354),
sigma_4(690) mod 690 = 668 (not 362). Nothing is outside Lean.
-/
import Mathlib

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

lemma A196226_sigma_prime {p : ℕ} (hp : p.Prime) (k : ℕ) : σ k p = 1 + p ^ k := by
  have := sigma_apply_prime_pow (k := k) (i := 1) hp
  simp [Finset.sum_range_succ] at this
  rw [this]

lemma A196226_sigma690 (k : ℕ) : σ k 690 = (1 + 2 ^ k) * (1 + 3 ^ k) * (1 + 5 ^ k) * (1 + 23 ^ k) := by
  have hm := (isMultiplicative_sigma (k := k))
  rw [show (690 : ℕ) = 2 * 3 * 5 * 23 by norm_num,
    hm.map_mul_of_coprime (by norm_num), hm.map_mul_of_coprime (by norm_num),
    hm.map_mul_of_coprime (by norm_num),
    A196226_sigma_prime (by norm_num), A196226_sigma_prime (by norm_num),
    A196226_sigma_prime (by norm_num), A196226_sigma_prime (by norm_num)]

theorem A196226_690_mem : σ 1 690 % 690 = 3 + 690 / 2 := by
  rw [A196226_sigma690]; norm_num

theorem A196226_conjectures_false :
    σ 1 690 % 690 = 3 + 690 / 2 ∧ 690 ≥ 38 ∧
    σ 2 690 % 690 ≠ (5 + 690 / 2) % 690 ∧
    σ 3 690 % 690 ≠ (9 + 690 / 2) % 690 ∧
    σ 4 690 % 690 ≠ (17 + 690 / 2) % 690 := by
  simp only [A196226_sigma690]; norm_num
