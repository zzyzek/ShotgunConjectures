import Mathlib

/-!
# OEIS A225004: a(n) divides n^2

A225004: `a(n)` is the largest multiple of `n` with fewer than `2 τ(n)` divisors
(`a n = sSup {m | n ∣ m ∧ τ m < 2 τ n}`, `τ m = #m.divisors`).

Checked: `A225004_main : 1 ≤ n → a n ∣ n ^ 2` (and `a_good`: `a n` is in the set, so the maximum
exists). Key lemma `dvd_sq_of_good`: a positive multiple `m` of `n` with `τ m < 2 τ n` divides `n^2`,
since `v_p(m) > 2 v_p(n)` would give `τ m ≥ (2 v_p(n) + 2) τ(n / p^{v_p n}) = 2 τ n`.
Not checked: nothing beyond reading the definition.
-/

namespace A225004

open ArithmeticFunction

def tau (n : ℕ) : ℕ := n.divisors.card

theorem tau_split (m p : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    tau m = (m.factorization p + 1) * tau (ordCompl[p] m) := by
  have hc : Nat.Coprime (p ^ m.factorization p) (ordCompl[p] m) :=
    (Nat.coprime_ordCompl hp hm).pow_left _
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p]
  unfold tau
  rw [Nat.Coprime.card_divisors_mul hc, ← sigma_zero_apply, sigma_zero_apply_prime_pow hp]

theorem dvd_sq_of_good (n m : ℕ) (hn : 1 ≤ n) (hm : m ≠ 0) (hnm : n ∣ m)
    (h : tau m < 2 * tau n) : m ∣ n ^ 2 := by
  rw [← Nat.factorization_le_iff_dvd hm (by positivity)]
  intro p
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hp : p.Prime := by
    by_contra hp
    have := Nat.factorization_eq_zero_of_not_prime m hp; omega
  rw [Nat.factorization_pow] at hlt
  simp only [Finsupp.smul_apply, smul_eq_mul] at hlt
  have hn0 : n ≠ 0 := by omega
  have h1 := tau_split m p hp hm
  have h2 := tau_split n p hp hn0
  have hd : ordCompl[p] n ∣ ordCompl[p] m := Nat.ordCompl_dvd_ordCompl_of_dvd hnm p
  have hm' : ordCompl[p] m ≠ 0 := by
    have := Nat.ordCompl_pos p hm; omega
  have h3 : tau (ordCompl[p] n) ≤ tau (ordCompl[p] m) :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hm' hd)
  have h4 : 2 * (n.factorization p + 1) ≤ m.factorization p + 1 := by omega
  have h5 : 2 * tau n ≤ tau m := by
    rw [h1, h2, ← mul_assoc]
    exact Nat.mul_le_mul h4 h3
  omega

open Classical in
/-- A225004. -/
noncomputable def a (n : ℕ) : ℕ := sSup {m | n ∣ m ∧ tau m < 2 * tau n}

theorem tau_pos (n : ℕ) (hn : 1 ≤ n) : 0 < tau n := by
  unfold tau; exact Finset.card_pos.mpr ⟨1, by simp; omega⟩

theorem bdd (n : ℕ) (hn : 1 ≤ n) : BddAbove {m | n ∣ m ∧ tau m < 2 * tau n} := by
  refine ⟨n ^ 2, fun m ⟨hnm, h⟩ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  · exact Nat.le_of_dvd (by positivity) (dvd_sq_of_good n m hn (by omega) hnm h)

theorem a_good (n : ℕ) (hn : 1 ≤ n) : n ∣ a n ∧ tau (a n) < 2 * tau n :=
  Nat.sSup_mem (s := {m | n ∣ m ∧ tau m < 2 * tau n}) ⟨n, dvd_refl n, by have := tau_pos n hn; omega⟩ (bdd n hn)

theorem A225004_main (n : ℕ) (hn : 1 ≤ n) : a n ∣ n ^ 2 := by
  obtain ⟨h1, h2⟩ := a_good n hn
  have hge : n ≤ a n := le_csSup (bdd n hn) ⟨dvd_refl n, by have := tau_pos n hn; omega⟩
  exact dvd_sq_of_good n (a n) hn (by omega) h1 h2
