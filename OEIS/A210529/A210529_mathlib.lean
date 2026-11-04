/-
OEIS A210529, Mathlib proof.

Main theorem `A210529_main`: for every prime p there is a prime a ≠ p
(in fact a > p) such that every prime ℓ below √p (ℓ^2 < p) divides
a^2 - p^2. Hence the search in the definition of a(n) (smallest such
prime, or 1) terminates for every n: a(n) is defined for all n, which is
the README result. The theorem gives infinitely many such a (a > m for
every bound m), so a smallest one exists by well-foundedness of ℕ.

Proof: p is coprime to (p - 1)!, so Dirichlet's theorem (Mathlib,
`Nat.forall_exists_prime_gt_and_modEq`) gives a prime a > p with
a ≡ p (mod (p - 1)!). Every prime ℓ with ℓ^2 < p is < p, so ℓ divides
(p - 1)!, hence a - p, hence a^2 - p^2.

Reading: the definition's "a(n) is 1 or the smallest prime" is read as
"the smallest number among 1 and the primes a ≠ p with the property"; the
existence of such a prime (proved here) settles definedness. Divisibility
is stated in ℤ, which is the same as divisibility of |a^2 - p^2|.

Not checked: nothing beyond the reading above.
-/
import Mathlib

theorem A210529_main (p m : ℕ) (hp : p.Prime) :
    ∃ a, a.Prime ∧ a ≠ p ∧ m < a ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ^ 2 < p → (ℓ : ℤ) ∣ (a : ℤ) ^ 2 - (p : ℤ) ^ 2 := by
  have hcop : p.Coprime (p - 1).factorial :=
    hp.coprime_factorial_of_lt (by have := hp.two_le; omega)
  obtain ⟨a, ha, haP, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max m p) (Nat.factorial_ne_zero (p - 1)) hcop
  refine ⟨a, haP, by omega, by omega, ?_⟩
  intro ℓ hℓ hℓp
  have hℓlt : ℓ < p := by nlinarith [hℓ.two_le]
  have hℓf : ℓ ∣ (p - 1).factorial := Nat.dvd_factorial hℓ.pos (by omega)
  have hdiv : (p - 1).factorial ∣ a - p := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  have h1 : (ℓ : ℤ) ∣ (a : ℤ) - p := by
    have := Int.natCast_dvd_natCast.mpr (hℓf.trans hdiv)
    rwa [Nat.cast_sub (by omega)] at this
  have : (a : ℤ) ^ 2 - (p : ℤ) ^ 2 = ((a : ℤ) - p) * ((a : ℤ) + p) := by ring
  rw [this]
  exact h1.mul_right _
