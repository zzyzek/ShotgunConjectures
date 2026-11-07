/-
OEIS A214074: a(n) = least m > 0 such that 2^n - m and 3^n - m are coprime.
Conjecture (entry comment): a(n) = 3 if and only if n = 330k - 209 for some
k ≥ 1.

Both directions are false.
* "if" fails at n₁ = 3438721 = 330·10421 - 209: the primes 23, 331 and
  487891 divide gcd(2^n₁ - m, 3^n₁ - m) for m = 1, 2, 3 respectively, so
  a(n₁) ≥ 4 (`A214074_if_false`, fully checked here).
* "only if" fails at n₂ = 1186095 ≡ 75 (mod 330): the primes 88681 and
  1210483 divide the gcds for m = 1, 2, so a(n₂) ≥ 3 (`A214074_n2_ge3`,
  checked here); a(n₂) = 3 also needs gcd(2^n₂ - 3, 3^n₂ - 3) = 1, a gcd of
  numbers with about 1.9 million bits, computed with PARI/GP and NOT checked
  in this file.

Definitions.  `A214074 n` = `Nat.find` of the least m > 0 with
Int.gcd (2^n - m) (3^n - m) = 1 (integers, so no truncated subtraction);
m = 2^n + 1 shows such m exists.  Residues 2^n mod p are computed with
`OpenProblemsLib.powMod` (square-and-multiply) and `decide +kernel`.
-/
import Mathlib
import OpenProblemsLib.PowMod

open OpenProblemsLib

theorem A214074_exists (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Int.gcd ((2 : ℤ) ^ n - m) ((3 : ℤ) ^ n - m) = 1 := by
  refine ⟨2 ^ n + 1, Nat.succ_pos _, ?_⟩
  have hc : (((2 ^ n + 1 : ℕ)) : ℤ) = (2 : ℤ) ^ n + 1 := by push_cast; ring
  rw [hc]
  have : (2 : ℤ) ^ n - ((2 : ℤ) ^ n + 1) = -1 := by ring
  rw [this]
  simp [Int.gcd]

open Classical in
/-- OEIS A214074: least m > 0 with gcd(2^n - m, 3^n - m) = 1. -/
noncomputable def A214074 (n : ℕ) : ℕ := Nat.find (A214074_exists n)

/-- If p > 1 divides 2^n - m and 3^n - m (given as residues of powers), the
gcd is not 1. -/
theorem gcd_ne_one_of_res (n m p : ℕ) (hp : 1 < p)
    (h2 : 2 ^ n % p = m % p) (h3 : 3 ^ n % p = m % p) :
    Int.gcd ((2 : ℤ) ^ n - m) ((3 : ℤ) ^ n - m) ≠ 1 := by
  intro hg
  have d2 : (p : ℤ) ∣ (2 : ℤ) ^ n - m := by
    have := (show m ≡ 2 ^ n [MOD p] from h2.symm).dvd
    simpa using this
  have d3 : (p : ℤ) ∣ (3 : ℤ) ^ n - m := by
    have := (show m ≡ 3 ^ n [MOD p] from h3.symm).dvd
    simpa using this
  have hd : (p : ℤ) ∣ ((Int.gcd ((2 : ℤ) ^ n - m) ((3 : ℤ) ^ n - m) : ℕ) : ℤ) :=
    Int.dvd_coe_gcd d2 d3
  rw [hg] at hd
  have : p ∣ 1 := by exact_mod_cast hd
  have := Nat.le_of_dvd one_pos this
  omega

/-- a(n) ≥ k + 1 when every m in 1..k has a common prime-power witness. -/
theorem A214074_ge (n k : ℕ) (h : ∀ m, 0 < m → m ≤ k →
    Int.gcd ((2 : ℤ) ^ n - m) ((3 : ℤ) ^ n - m) ≠ 1) : k + 1 ≤ A214074 n := by
  classical
  unfold A214074
  rw [Nat.le_find_iff]
  intro m hm ⟨hpos, hg⟩
  exact h m hpos (by omega) hg

theorem A214074_n1_ge4 : 4 ≤ A214074 3438721 := by
  apply A214074_ge 3438721 3
  intro m hpos hm
  interval_cases m
  · exact gcd_ne_one_of_res _ _ 23 (by norm_num)
      (by rw [← powMod_eq]; decide +kernel) (by rw [← powMod_eq]; decide +kernel)
  · exact gcd_ne_one_of_res _ _ 331 (by norm_num)
      (by rw [← powMod_eq]; decide +kernel) (by rw [← powMod_eq]; decide +kernel)
  · exact gcd_ne_one_of_res _ _ 487891 (by norm_num)
      (by rw [← powMod_eq]; decide +kernel) (by rw [← powMod_eq]; decide +kernel)

/-- The "if" direction of the conjecture is false. -/
theorem A214074_if_false :
    ¬ ∀ n : ℕ, (∃ k : ℕ, 1 ≤ k ∧ n = 330 * k - 209) → A214074 n = 3 := by
  intro h
  have := h 3438721 ⟨10421, by norm_num, by norm_num⟩
  have := A214074_n1_ge4
  omega

/-- n₂ = 1186095 is not of the form 330k - 209, yet a(n₂) ≥ 3.  (a(n₂) = 3,
which needs gcd(2^n₂ - 3, 3^n₂ - 3) = 1, is checked outside Lean.) -/
theorem A214074_n2_ge3 : 3 ≤ A214074 1186095 := by
  apply A214074_ge 1186095 2
  intro m hpos hm
  interval_cases m
  · exact gcd_ne_one_of_res _ _ 88681 (by norm_num)
      (by rw [← powMod_eq]; decide +kernel) (by rw [← powMod_eq]; decide +kernel)
  · exact gcd_ne_one_of_res _ _ 1210483 (by norm_num)
      (by rw [← powMod_eq]; decide +kernel) (by rw [← powMod_eq]; decide +kernel)

theorem A214074_n2_not_form : ¬ ∃ k : ℕ, 1 ≤ k ∧ 1186095 = 330 * k - 209 := by
  rintro ⟨k, hk, h⟩
  omega
