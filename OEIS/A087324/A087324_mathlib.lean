/-
OEIS A087324, Mathlib proof.

A087324: numbers n such that n and its 9's complement have the same prime
signature. The 9's complement of a d-digit n is 10^d - 1 - n. Conjecture:
(1) the sequence is infinite; (2) for every prime signature there is a term.

Definitions: `A087324_sig n` = the multiset of exponents in the prime
factorization of n (Mathlib `Nat.factorization` over `Nat.primeFactors`);
`A087324_comp n` = 10^d - 1 - n with d = `(Nat.digits 10 n).length`.

Main theorem `A087324_main`:
* no n ≥ 1 with sig n = sig (comp n) has a nonempty all-even signature;
* in particular no term has signature {2} (that of p^2), although
  sig 4 = {2} is a prime signature. So conjecture (2) is false.
This is the README result; the step "all exponents even ⇒ square" is proved
here (Mathlib `Nat.isSquare_iff_even_factorization`). Conjecture (1) is not
addressed (open). Nothing else is outside Lean.
-/
import Mathlib

/-- The prime signature of n as a multiset of exponents. -/
def A087324_sig (n : ℕ) : Multiset ℕ := n.primeFactors.val.map n.factorization

/-- 9's complement of n: 10^d - 1 - n, d = number of decimal digits of n. -/
def A087324_comp (n : ℕ) : ℕ := 10 ^ (Nat.digits 10 n).length - 1 - n

theorem A087324_isSquare (n : ℕ) (h : ∀ e ∈ A087324_sig n, Even e) : IsSquare n := by
  by_cases hn : n = 0
  · subst hn; exact ⟨0, rfl⟩
  rw [Nat.isSquare_iff_even_factorization]
  intro p hp
  by_cases hd : p ∣ n
  · exact h _ (Multiset.mem_map_of_mem _ (Nat.mem_primeFactors.2 ⟨hp, hd, hn⟩))
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]; exact ⟨0, rfl⟩

theorem A087324_sq_mod4 (x : ℕ) : x * x % 4 = 0 ∨ x * x % 4 = 1 := by
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega

theorem A087324_main :
    (∀ n, 1 ≤ n → A087324_sig n = A087324_sig (A087324_comp n) →
      ¬ (A087324_sig n ≠ 0 ∧ ∀ e ∈ A087324_sig n, Even e)) ∧
    A087324_sig 4 = {2} ∧
    ¬ ∃ n, 1 ≤ n ∧ A087324_sig n = A087324_sig (A087324_comp n) ∧ A087324_sig n = {2} := by
  have key : ∀ n, 1 ≤ n → A087324_sig n = A087324_sig (A087324_comp n) →
      ¬ (A087324_sig n ≠ 0 ∧ ∀ e ∈ A087324_sig n, Even e) := by
    rintro n hn hsig ⟨hne, hev⟩
    obtain ⟨x, hx⟩ := A087324_isSquare n hev
    obtain ⟨y, hy⟩ := A087324_isSquare (A087324_comp n) (hsig ▸ hev)
    have hc0 : A087324_comp n ≠ 0 := by
      intro h0
      rw [h0] at hsig
      exact hne (by rw [hsig]; simp [A087324_sig])
    set d := (Nat.digits 10 n).length with hd
    have hlt : n < 10 ^ d := Nat.lt_base_pow_length_digits (by norm_num)
    have hcomp : A087324_comp n = 10 ^ d - 1 - n := rfl
    have hd0 : d ≠ 0 := by
      intro h0
      rw [hd, List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero] at h0
      omega
    rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · have h1 : d = 1 := by omega
      rw [h1, pow_one] at hlt hcomp
      rw [hcomp] at hy
      have hx3 : x ≤ 3 := by nlinarith
      have hy9 : y * y ≤ 9 := by omega
      have hy3 : y ≤ 3 := by nlinarith
      interval_cases x <;> interval_cases y <;> omega
    · have h4 : 10 ^ d % 4 = 0 := by
        obtain ⟨k, hk⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
        rw [hk, pow_add]; norm_num [Nat.mul_mod]
      have := A087324_sq_mod4 x
      have := A087324_sq_mod4 y
      omega
  refine ⟨key, ?_, ?_⟩
  · have h1 : (4 : ℕ).primeFactors = {2} := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl]
      exact Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two
    have h2 : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.prime_two.factorization_self]
      rfl
    simp [A087324_sig, h1, h2]
  · rintro ⟨n, hn, hsig, h2⟩
    exact key n hn hsig ⟨by rw [h2]; simp, by rw [h2]; simp⟩
