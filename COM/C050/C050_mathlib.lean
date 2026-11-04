import OpenProblemsLib
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-
COM-C050 (Mathlib). Coman's conjecture 50: there are infinitely many base-3 Fermat
pseudoprimes of the form (3^(4k+2) − 1)/8. README result: true.

Main theorem `C050_main`: the set {N | N is a Fermat pseudoprime to base 3 (Mathlib
`Nat.FermatPsp N 3`) and N = (3^(4k+2) − 1)/8 for some natural k} is infinite.
Proof: Cipolla's theorem (library `cipolla`, Mathlib's proof made public) with b = 3 and a
prime p = 2k + 1 ≥ 5 (so p ∤ 3·8): (3^(2p) − 1)/(3² − 1) is a base-3 pseudoprime larger
than p; primes are unbounded (Mathlib `Nat.exists_infinite_primes`).

Outside Lean: nothing. (Template certificate/C050_mathlib.lean.in, tools/lean_expand.py.)
-/

open OpenProblemsLib

theorem C050_main : Set.Infinite {N : ℕ | N.FermatPsp 3 ∧ ∃ k : ℕ, N = (3 ^ (4 * k + 2) - 1) / 8} := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 25)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hnd : ¬ p ∣ 3 * (3 ^ 2 - 1) := Nat.not_dvd_of_pos_of_lt (by norm_num) (by norm_num; omega)
  obtain ⟨hpsp, hgt⟩ := cipolla (b := 3) (p := p) (by norm_num) hp (by omega) hnd
  refine ⟨_, ⟨hpsp, (p - 1) / 2, ?_⟩, by omega⟩
  rw [show 2 * p = 4 * ((p - 1) / 2) + 2 by omega]
  norm_num
