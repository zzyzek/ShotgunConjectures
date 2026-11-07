import Mathlib
import OpenProblemsLib.Dwork
import OpenProblemsLib.DworkLocal

/-!
# OEIS A165940 is an integer sequence

A165940: `∑_{n ≥ 0} a(n) x^n / 2^(n^2+n) = exp (∑_{n ≥ 1} x^n / (n 2^(n^2)))`.
Here `a n = 2^(n^2+n) * expQ u n` with `u m = 1 / 2^(m^2)` and `expQ` the coefficient recurrence
of `exp (∑ u m x^m / m)` (library `OpenProblemsLib.DworkLocal`).

Checked: `A165940_int : ∀ n, ∃ z : ℤ, a n = z`.
* odd `p`: `u` satisfies the Gauss congruences at `p` (`(2^N)^N - (2^M)^M` is divisible by `p^a`
  for `N = m p^a`, `M = m p^(a-1)`), so `expQ u n` is `p`-integral by the p-local Dwork lemma
  `expQ_pint_of_LGq`;
* `p = 2`: `v_2 (expQ u n) ≥ -n^2 - v_2(n!)` by the recurrence, and `v_2(n!) ≤ n` (Legendre).
Not checked: that the OEIS g.f. means this recurrence (reading of `exp (∑ b x^n / n)`).
-/

namespace A165940

open OpenProblemsLib.Dwork OpenProblemsLib.DworkLocal

def u (m : ℕ) : ℚ := 1 / 2 ^ (m ^ 2)

def a (n : ℕ) : ℚ := 2 ^ (n ^ 2 + n) * expQ u n

theorem u_unit (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) : PV p 0 (u m) := by
  have h := PV_inv_coprime (p := p) 2 (m ^ 2)
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h))
  simpa [u] using h

theorem u_LGq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : LGq p u := by
  intro a m ha
  set N := m * p ^ a
  set M := m * p ^ (a - 1)
  have h := LGp_pow_self p hp.out (LGp_zpow p hp.out 2) 1 a m ha
  simp only [mul_one] at h
  have h2 : (p : ℤ) ^ a ∣ ((2 : ℤ) ^ M) ^ M - ((2 : ℤ) ^ N) ^ N := by
    have := h.neg_right; rwa [neg_sub] at this
  have e : u N - u M = (((((2 : ℤ) ^ M) ^ M - ((2 : ℤ) ^ N) ^ N : ℤ) : ℚ) * u N) * u M := by
    simp only [u]; push_cast
    rw [← pow_mul, ← pow_mul, ← sq, ← sq]
    field_simp
  rw [e]
  have := PV_mul (PV_mul (PV_dvd (p := p) a _ h2) (u_unit p hp2 N)) (u_unit p hp2 M)
  simpa using this

theorem two_adic : ∀ n : ℕ, PV 2 (-((n : ℤ) ^ 2) - padicValNat 2 n.factorial) (expQ u n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [expQ_zero]; simpa using PV_int (p := 2) 1
    · have key := expQ_succ u n
      have hS : PV 2 (-((n : ℤ) + 1) ^ 2 - padicValNat 2 n.factorial)
          (∑ j ∈ Finset.range (n + 1), u (j + 1) * expQ u (n - j)) := by
        apply PV_sum; intro j hj
        rw [Finset.mem_range] at hj
        have h1 : PV 2 (-((j : ℤ) + 1) ^ 2) (u (j + 1)) := by
          have := PV_inv_ppow (p := 2) ((j + 1) ^ 2); push_cast at this; simpa [u] using this
        have hv := vfact_mono (p := 2) (show n - j ≤ n by omega)
        refine PV_mono (PV_mul h1 (ih (n - j) (by omega))) ?_
        have hc : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by push_cast [show j ≤ n by omega]; ring
        push_cast; rw [hc]
        have hj' : (j : ℤ) ≤ n := by exact_mod_cast (show j ≤ n by omega)
        have hj0 : (0 : ℤ) ≤ j := by positivity
        nlinarith
      have hδ : expQ u (n + 1) = (∑ j ∈ Finset.range (n + 1), u (j + 1) * expQ u (n - j)) /
          ((n + 1 : ℕ) : ℚ) := by
        rw [eq_div_iff (by positivity)]; push_cast; rw [mul_comm]; exact key
      rw [hδ]
      have := PV_div_nat hS (n + 1) (by omega)
      rw [vfact_succ]; push_cast at this ⊢
      convert this using 1; ring

theorem vfact_le (n : ℕ) : padicValNat 2 n.factorial ≤ n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simp at this; omega

theorem A165940_int (n : ℕ) : ∃ z : ℤ, a n = z := by
  apply int_of_PV
  intro p hp
  have := Fact.mk hp
  rcases eq_or_ne p 2 with rfl | hp2
  · unfold a
    have h1 : PV 2 ((n : ℤ) ^ 2 + n) ((2 : ℚ) ^ (n ^ 2 + n)) := by
      have := PV_ppow (p := 2) (n ^ 2 + n); push_cast at this; simpa using this
    have h := PV_mul h1 (two_adic n)
    refine PV_mono h ?_
    have h' : ((padicValNat 2 n.factorial : ℕ) : ℤ) ≤ n := by exact_mod_cast vfact_le n
    linarith
  · have h1 : PV p 0 ((2 : ℚ) ^ (n ^ 2 + n)) := by simpa using PV_int (p := p) (2 ^ (n ^ 2 + n))
    have h2 := expQ_pint_of_LGq u (fun m _ => u_unit p hp2 m) (u_LGq p hp2) n
    simpa [a] using PV_mul h1 h2

