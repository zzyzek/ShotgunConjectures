/-
OEIS A125148, conjecture: for every odd x ≥ 1 not divisible by 5 there is a
prime p = z + x with z a multiple of 10.

Main theorem `A125148_conjecture`: for every natural x that is odd and not
divisible by 5, there is z > 0 with 10 ∣ z and z + x prime.  This is the
README result (with z positive, as in the entry's terms).  Proof: x is coprime
to 10, so Dirichlet's theorem (Mathlib `Nat.forall_exists_prime_gt_and_modEq`)
gives a prime p > x with p ≡ x (mod 10); take z = p − x.

Not checked: nothing outside Lean.
-/
import Mathlib

theorem A125148_conjecture (x : ℕ) (hodd : Odd x) (h5 : ¬ 5 ∣ x) :
    ∃ z : ℕ, 0 < z ∧ 10 ∣ z ∧ (z + x).Prime := by
  have h2 : Nat.Coprime x 2 := Nat.coprime_two_right.2 hodd
  have h5' : Nat.Coprime x 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm
  have hc : Nat.Coprime x 10 := by
    have : (10 : ℕ) = 2 * 5 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_right h2 h5'
  obtain ⟨p, hpx, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq x (by norm_num) hc
  refine ⟨p - x, by omega, ?_, ?_⟩
  · exact (Nat.modEq_iff_dvd' hpx.le).1 hmod.symm
  · rwa [Nat.sub_add_cancel hpx.le]
