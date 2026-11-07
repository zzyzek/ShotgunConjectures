import Mathlib
import OpenProblemsLib.Dwork
import OpenProblemsLib.DworkLocal

/-!
# OEIS A177430 / A177431: exp(sum b(n)^m x^n/n) is integral exactly for even m >= 0

A177431 = b is the least increasing sequence such that exp(sum b(n)^2 x^n/n) has integer
coefficients; it begins b = 1, 3, 4, 5, 6, ... and A177430 = b^2.

Main result.
* `A177431_iff` : for any b : ℕ → ℕ with b 1 = 1, b 2 = 3, b 4 = 5 and
  exp(sum b(n)^2 x^n/n) integral, and every integer m:
  exp(sum b(n)^m x^n/n) is integral iff m >= 0 and m is even.
  (A177430's form uses a(n)^(m/2) = b(n)^m.)

Series are handled by coefficient recurrences (`expQ` over ℚ, `expCoeff` over ℤ inputs) from the
shared library (Dwork's lemma, closure of Gauss congruences under powers).

Checked: the theorem above. Not checked in Lean: that the greedy definition gives b(1), b(2), b(4) =
1, 3, 5 (it is the entry's data, recomputed by certificate/greedy.py) and that it is integral at
m = 2 (its definition).
-/

open OpenProblemsLib.Dwork OpenProblemsLib.DworkLocal

lemma expQ_one (c : ℕ → ℚ) : expQ c 1 = c 1 := by
  have h := expQ_succ c 0
  simp [expQ_zero] at h
  simpa using h

lemma expQ_two (c : ℕ → ℚ) : 2 * expQ c 2 = c 1 * c 1 + c 2 := by
  have h := expQ_succ c 1
  simp [Finset.sum_range_succ, expQ_zero, expQ_one] at h
  linear_combination h

theorem A177431_iff (b : ℕ → ℕ) (hb1 : b 1 = 1) (hb2 : b 2 = 3) (hb4 : b 4 = 5)
    (hsq : ∀ n, ∃ z : ℤ, expCoeff (fun k => (b k : ℤ) ^ 2) n = z) (m : ℤ) :
    (∀ n, ∃ z : ℤ, expQ (fun k => (b k : ℚ) ^ m) n = z) ↔ (0 ≤ m ∧ Even m) := by
  constructor
  · intro h
    by_cases hm : m < 0
    · exfalso
      obtain ⟨z, hz⟩ := h 2
      have e := expQ_two (fun k => (b k : ℚ) ^ m)
      simp only [hb1, hb2, Nat.cast_one, one_zpow, mul_one, hz] at e
      have h3 : (0 : ℚ) < (3 : ℚ) ^ m := zpow_pos (by norm_num) m
      have h3' : (3 : ℚ) ^ m < 1 := zpow_lt_one_of_neg₀ (by norm_num) hm
      have hz1 : (z : ℚ) * 2 - 1 = (3 : ℚ) ^ m := by push_cast at e; linarith
      have : (0 : ℚ) < z * 2 - 1 := by linarith
      have : (z * 2 - 1 : ℚ) < 1 := by linarith
      have h1 : (0 : ℤ) < z * 2 - 1 := by exact_mod_cast (by push_cast; linarith : (0:ℚ) < (z * 2 - 1 : ℤ))
      have h2 : z * 2 - 1 < (1 : ℤ) := by exact_mod_cast (by push_cast; linarith : ((z * 2 - 1 : ℤ) : ℚ) < 1)
      omega
    · push Not at hm
      refine ⟨hm, ?_⟩
      obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = t := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
      have hcast : ∀ n, expQ (fun k => (b k : ℚ) ^ (t : ℤ)) n =
          expCoeff (fun k => (b k : ℤ) ^ t) n := by
        intro n
        rw [← expQ_cast]
        congr 1
        funext k
        push_cast
        rw [zpow_natCast]
      have hint : ∀ n, ∃ z : ℤ, expCoeff (fun k => (b k : ℤ) ^ t) n = z := by
        intro n; obtain ⟨z, hz⟩ := h n; exact ⟨z, by rw [← hcast]; exact hz⟩
      have hG := gauss_of_expCoeff_int _ hint 2 Nat.prime_two 2 1 (by norm_num)
      have hG' : (4 : ℤ) ∣ 5 ^ t - 3 ^ t := by
        have e1 : 1 * 2 ^ 2 = 4 := rfl
        have e2 : 1 * 2 ^ (2 - 1) = 2 := rfl
        simp only [e1, e2, hb4, hb2] at hG
        exact_mod_cast hG
      by_contra hodd
      rw [Int.not_even_iff_odd] at hodd
      obtain ⟨s, hs⟩ := hodd
      have ht : t = 2 * s.toNat + 1 := by omega
      rw [ht] at hG'
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr (by exact_mod_cast hG')
      push_cast at hz
      rw [pow_succ, pow_succ, pow_mul, pow_mul] at hz
      have h5 : (5 : ZMod 4) ^ 2 = 1 := by decide
      have h3 : (3 : ZMod 4) ^ 2 = 1 := by decide
      rw [h5, h3] at hz
      simp only [one_pow] at hz
      revert hz; decide
  · rintro ⟨hm, ⟨j, hj⟩⟩
    have hG : ∀ p : ℕ, p.Prime → LGp p (fun k => ((b k : ℤ) ^ 2) ^ j.toNat) :=
      fun p hp => LGp_pow (gauss_of_expCoeff_int _ hsq p hp) j.toNat
    intro n
    obtain ⟨z, hz⟩ := expCoeff_int_of_gauss _ hG n
    refine ⟨z, ?_⟩
    rw [← hz, ← expQ_cast]
    congr 1
    funext k
    have : m = ((2 * j.toNat : ℕ) : ℤ) := by push_cast; omega
    rw [this, zpow_natCast]
    push_cast
    ring
