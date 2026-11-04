import OpenProblemsLib
import Mathlib.NumberTheory.PrimesCongruentOne

/-
COM-C162 (Mathlib; also covers P103). Coman's conjecture 162: there are infinitely many
Poulet numbers (42m + 1)(42n + 1). README result: true.

Main theorem `C162_main`: the set {N | N is a Fermat pseudoprime to base 2 (Mathlib
`Nat.FermatPsp N 2`) and N = (42m + 1)(42n + 1) with m, n ≥ 1} is infinite. (m, n ≥ 1 makes
both factors nontrivial; 5461 = 127 · 43 is the case p = 7.)
Proof: for a prime p ≡ 1 (mod 6), p > 6, Cipolla's theorem (library `cipolla_fermatPsp`,
Mathlib's proof made public) with b = 2 makes (2^p − 1)((2^p + 1)/3) a base-2 pseudoprime
larger than p, and both factors are ≡ 1 (mod 42) because 2^p ≡ 2 (mod 126); there are arbitrarily large primes ≡ 1
(mod 6) (Mathlib `Nat.exists_prime_gt_modEq_one`).

Outside Lean: nothing. (Template certificate/C162_mathlib.lean.in, tools/lean_expand.py.)
-/

open OpenProblemsLib

theorem pow_mod63 (p : ℕ) (hp : p % 6 = 1) : 2 ^ p % 63 = 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, p = 6 * t + 1 := ⟨p / 6, by omega⟩
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem first (p : ℕ) (hp : p % 6 = 1) : (2 ^ p - 1) % 42 = 1 := by
  have h1 := pow_mod63 p hp
  have h2 : 2 ^ p % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    rw [pow_succ]; simp
  generalize 2 ^ p = x at *
  omega

theorem second (p : ℕ) (hp : p % 6 = 1) : (2 ^ p + 1) % 3 = 0 ∧ ((2 ^ p + 1) / 3) % 42 = 1 := by
  have h1 := pow_mod63 p hp
  have h2 : 2 ^ p % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    rw [pow_succ]; simp
  generalize 2 ^ p = x at *
  omega

theorem C162_main : Set.Infinite {N : ℕ | N.FermatPsp 2 ∧
    ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ N = (42 * m + 1) * (42 * n + 1)} := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨p, hp, hpM, hp6⟩ := Nat.exists_prime_gt_modEq_one (k := 6) (M + 7) (by norm_num)
  have h61 : p % 6 = 1 := hp6
  have hnd : ¬ p ∣ 2 * (2 ^ 2 - 1) := Nat.not_dvd_of_pos_of_lt (by norm_num) (by norm_num; omega)
  have hpsp := cipolla_fermatPsp (b := 2) (p := p) le_rfl hp (by omega) hnd
  have hgt := cipolla_gt (b := 2) (p := p) le_rfl (by omega)
  have e : cipollaNum 2 p = (2 ^ p - 1) * ((2 ^ p + 1) / 3) := by
    simp [cipollaNum]
  have h1 := first p h61
  have h2 := second p h61
  have hbig : 2 ^ 7 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨cipollaNum 2 p, ⟨hpsp, (2 ^ p - 1) / 42, (2 ^ p + 1) / 3 / 42, ?_, ?_, ?_⟩, by omega⟩
  · omega
  · omega
  · rw [e]
    congr 1
    · omega
    · omega
