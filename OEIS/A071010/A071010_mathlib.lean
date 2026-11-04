/-
OEIS A071010 (sigma(k)/4 for k not a sum of two squares), conjecture: if n is
not a sum of two squares then sigma(n) ≡ 0 (mod 4).

Main theorem `A071010_conjecture`: for every natural n that is not of the form
x^2 + y^2 (x, y natural), 4 divides σ(n) (Mathlib `ArithmeticFunction.sigma 1`).
This is the README result.

Proof: by the two-squares theorem (Mathlib `Nat.eq_sq_add_sq_iff`) some prime
q ≡ 3 (mod 4) divides n to an odd power e.  σ is multiplicative, so
σ(q^e) ∣ σ(n), and σ(q^e) = (1 + q)(1 + q^2 + ... + q^(e-1)) with 4 ∣ 1 + q.

Not checked: nothing outside Lean.
-/
import Mathlib

open ArithmeticFunction Finset

/-- Σ_{i < 2j} q^i = (1 + q)·Σ_{i < j} q^(2i). -/
lemma geom_even (q j : ℕ) :
    ∑ i ∈ range (2 * j), q ^ i = (1 + q) * ∑ i ∈ range j, q ^ (2 * i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

theorem A071010_conjecture (n : ℕ) (h : ¬ ∃ x y : ℕ, n = x ^ 2 + y ^ 2) :
    4 ∣ sigma 1 n := by
  have hn : n ≠ 0 := by rintro rfl; exact h ⟨0, 0, by norm_num⟩
  rw [Nat.eq_sq_add_sq_iff] at h
  push Not at h
  obtain ⟨q, hq, hq3, hodd⟩ := h
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  set e := n.factorization q with he
  have hev : ¬ Even e := by rw [he, Nat.factorization_def n hqp]; exact hodd
  obtain ⟨j, hj⟩ : ∃ j, e + 1 = 2 * j := by
    rcases Nat.not_even_iff_odd.mp hev with ⟨t, ht⟩; exact ⟨t + 1, by omega⟩
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self n q
  have hcop : Nat.Coprime (q ^ e) (n / q ^ e) :=
    (Nat.coprime_ordCompl hqp hn).pow_left e
  have hmul : sigma 1 n = sigma 1 (q ^ e) * sigma 1 (n / q ^ e) := by
    conv_lhs => rw [← hsplit]
    exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have hpow : sigma 1 (q ^ e) = (1 + q) * ∑ i ∈ range j, q ^ (2 * i) := by
    rw [sigma_one_apply_prime_pow hqp, hj, geom_even]
  have h4 : 4 ∣ 1 + q := by omega
  rw [hmul, hpow]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h4 _) _
