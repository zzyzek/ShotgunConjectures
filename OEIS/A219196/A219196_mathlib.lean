/-
OEIS A219196: a(n) = A027642(A131577(n)), the denominator of the Bernoulli
number B_{A131577(n)}, where A131577 = 0, 1, 2, 4, 8, ... (A131577(n) = 2^(n-1)
for n ≥ 1).
Conjecture (entry comment): a(15) = a(16) = 131070 and
a(17), ..., a(32) = 8589934590.

Proof.  von Staudt–Clausen (Mathlib `Bernoulli.vonStaudt_clausen` plus
`Bernoulli.dvd_den_bernoulli`) gives, for k ≥ 1, den B_{2k} = ∏ p over primes
p with p - 1 ∣ 2k (library `OpenProblemsLib.BernoulliDen.bernoulli_den_eq_prod`).  For 2k = 2^m, p - 1 ∣ 2^m forces
p = 2^j + 1 with j ≤ m; for m ≤ 31 the primes of this form are 2, 3, 5, 17,
257, 65537 (65537 needs j = 16).  Products: 2·3·5·17·257 = 131070 and
131070·65537 = 8589934590.

Main theorems: `A219196_15`, `A219196_16`, `A219196_17_32`.
Not checked here: nothing beyond reading A027642 as Mathlib's
`(bernoulli n).den` (the sign convention for B₁ does not change denominators).
-/
import Mathlib
import OpenProblemsLib.BernoulliDen

open Finset OpenProblemsLib.BernoulliDen

/-- Primes p with p - 1 ∣ 2^m, m ≤ 31, are among 2, 3, 5, 17, 257, 65537. -/
theorem fermat_like (m p : ℕ) (hm : m ≤ 31) (hp : p.Prime) (hd : (p - 1) ∣ 2 ^ m) :
    ∃ j, j ≤ m ∧ p = 2 ^ j + 1 ∧ (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 8 ∨ j = 16) := by
  obtain ⟨j, hj, hpj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have h2 := hp.two_le
  have hpe : p = 2 ^ j + 1 := by omega
  refine ⟨j, hj, hpe, ?_⟩
  subst hpe
  have : j ≤ 31 := le_trans hj hm
  interval_cases j <;> first | omega | (norm_num at hp)

/-- A131577: 0, then 2^(n-1). -/
def A131577 (n : ℕ) : ℕ := if n = 0 then 0 else 2 ^ (n - 1)

/-- A219196(n) = denominator of B_{A131577(n)}. -/
def A219196 (n : ℕ) : ℕ := (bernoulli (A131577 n)).den

theorem vscSet_pow (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 31) :
    vscSet (2 ^ (m - 1)) = ((({0, 1, 2, 4, 8, 16} : Finset ℕ).filter (· ≤ m)).image
      (fun j => 2 ^ j + 1)) := by
  have h2 : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [← pow_succ']; congr 1; omega
  ext p
  simp only [vscSet, Finset.mem_filter, Finset.mem_range, Finset.mem_image, h2]
  constructor
  · rintro ⟨-, hp, hd⟩
    obtain ⟨j, hj, rfl, hj6⟩ := fermat_like m p hm hp hd
    exact ⟨j, ⟨by simp only [Finset.mem_insert, Finset.mem_singleton]; omega, hj⟩, rfl⟩
  · rintro ⟨j, ⟨hj6, hjm⟩, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj6
    refine ⟨?_, ?_, ?_⟩
    · have : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hjm
      omega
    · rcases hj6 with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    · simp only [Nat.add_sub_cancel]
      exact Nat.pow_dvd_pow 2 hjm

theorem A219196_eq (n : ℕ) (h2 : 2 ≤ n) (h32 : n ≤ 32) :
    A219196 n = ∏ p ∈ ((({0, 1, 2, 4, 8, 16} : Finset ℕ).filter (· ≤ n - 1)).image
      (fun j => 2 ^ j + 1)), p := by
  unfold A219196 A131577
  have hn : n ≠ 0 := by omega
  simp only [hn, ↓reduceIte]
  have h : 2 ^ (n - 1) = 2 * 2 ^ (n - 1 - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h, bernoulli_den_eq_prod _ (by positivity), vscSet_pow (n - 1) (by omega) (by omega)]

theorem A219196_15 : A219196 15 = 131070 := by
  rw [A219196_eq 15 (by norm_num) (by norm_num)]; decide

theorem A219196_16 : A219196 16 = 131070 := by
  rw [A219196_eq 16 (by norm_num) (by norm_num)]; decide

theorem A219196_17_32 (n : ℕ) (h1 : 17 ≤ n) (h2 : n ≤ 32) : A219196 n = 8589934590 := by
  rw [A219196_eq n (by omega) h2]
  have : ((({0, 1, 2, 4, 8, 16} : Finset ℕ).filter (· ≤ n - 1))) = {0, 1, 2, 4, 8, 16} := by
    ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [this]; decide
