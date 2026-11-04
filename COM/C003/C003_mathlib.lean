import OpenProblemsLib
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-
COM-C003 (Mathlib). Coman's conjecture 3: for every integer n > 1 the number
(n^(nk+k+n−1) − 1)/(n² − 1) is a Fermat pseudoprime to base n for infinitely many k.
README result: true.

Main theorem `C003_main`: for every natural n > 1 the set of natural k with
(n^(nk+k+n−1) − 1)/(n² − 1) a Fermat pseudoprime to base n (Mathlib `Nat.FermatPsp _ n`)
is infinite.
Proof: take a prime p ≡ −1 (mod n+1) (Dirichlet's theorem, Mathlib
`Nat.forall_exists_prime_gt_and_modEq`) with p > n(n² − 1) and p large; then
k = 2(p+1)/(n+1) − 1 gives nk + k + n − 1 = 2p, and Cipolla's theorem (library `cipolla`,
Mathlib's proof made public) makes (n^(2p) − 1)/(n² − 1) a base-n pseudoprime.

Outside Lean: nothing. (Template certificate/C003_mathlib.lean.in, tools/lean_expand.py.)
-/

open OpenProblemsLib

theorem C003_main (n : ℕ) (hn : 1 < n) :
    Set.Infinite {k : ℕ | Nat.FermatPsp ((n ^ (n * k + k + n - 1) - 1) / (n ^ 2 - 1)) n} := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  have hcop : Nat.Coprime n (n + 1) := by simp
  obtain ⟨p, hpgt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq ((M + 1) * (n + 1) + n * (n ^ 2 - 1) + 2)
      (q := n + 1) (a := n) (by omega) hcop
  have hpm : p % (n + 1) = n := by
    have : p % (n + 1) = n % (n + 1) := hpmod
    rwa [Nat.mod_eq_of_lt (by omega : n < n + 1)] at this
  -- p + 1 = (n + 1) m
  set m := p / (n + 1) + 1 with hm
  have hpm1 : p + 1 = (n + 1) * m := by
    have := Nat.div_add_mod p (n + 1)
    rw [hm]; rw [hpm] at this; linarith
  have hn2 : 0 < n * (n ^ 2 - 1) := by
    have : 4 ≤ n ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  have hnd : ¬ p ∣ n * (n ^ 2 - 1) := Nat.not_dvd_of_pos_of_lt hn2 (by omega)
  have hMm : M + 1 < m := by
    by_contra hle
    rw [not_lt] at hle
    have : (n + 1) * m ≤ (n + 1) * (M + 1) := Nat.mul_le_mul_left _ hle
    nlinarith
  obtain ⟨hpsp, _⟩ := cipolla (b := n) (p := p) (by omega) hp (by omega) hnd
  refine ⟨2 * m - 1, ?_, by omega⟩
  show Nat.FermatPsp ((n ^ (n * (2 * m - 1) + (2 * m - 1) + n - 1) - 1) / (n ^ 2 - 1)) n
  have e : n * (2 * m - 1) + (2 * m - 1) + n - 1 = 2 * p := by
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm'] at hpm1 ⊢
    rw [show 2 * (m' + 1) - 1 = 2 * m' + 1 by omega]
    have : p = n * m' + n + m' := by nlinarith
    rw [this]
    ring_nf
    omega
  rw [e]
  exact hpsp
