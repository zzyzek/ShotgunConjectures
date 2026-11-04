/-
Coman C138, Mathlib proof.

Main theorem `C138_main`: for every Fermat pseudoprime P to base 2
(a Poulet number, `Nat.FermatPsp P 2`) the set of primes p with
p^2 = n * (P - 1) + 1 for some n ≥ 1 is infinite.

This is the README result (Coman's conjecture 138) verbatim. The proof
uses Mathlib's `Nat.infinite_setOfPred_prime_modEq_one` (infinitely many
primes p ≡ 1 mod k): p = (P - 1) t + 1 gives n = t ((P - 1) t + 2).
In fact only 1 < P is used, so the statement holds for every P ≥ 2.

Not checked: nothing; the whole statement is proved here.
-/
import Mathlib

theorem C138_sq_form {k p : ℕ} (hp : p.Prime) (h : p ≡ 1 [MOD k]) :
    ∃ n ≥ 1, p ^ 2 = n * k + 1 := by
  have h1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' h1).mp h.symm
  have hp2 := hp.two_le
  refine ⟨t * (k * t + 2), ?_, ?_⟩
  · have : t ≠ 0 := by
      rintro rfl
      omega
    have : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr this
    nlinarith
  · have hp' : p = k * t + 1 := by omega
    subst hp'
    ring

theorem C138_main (P : ℕ) (hP : Nat.FermatPsp P 2) :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ n ≥ 1, p ^ 2 = n * (P - 1) + 1} := by
  have hk : P - 1 ≠ 0 := by
    have := hP.2.2
    omega
  refine (Nat.infinite_setOfPred_prime_modEq_one hk).mono ?_
  rintro p ⟨hp, hmod⟩
  exact ⟨hp, C138_sq_form hp hmod⟩
