/-
OEIS A137328: a(n) = prime(n) - primorial(k), k maximal with primorial(k) ≤ prime(n).
Conjecture: every prime occurs. False: 2 never occurs.

For every prime p ≥ 2 the maximal k has k ≥ 1 (primorial(1) = 2 ≤ p), so the
subtracted primorial P is even and ≥ 2. If p - P = 2 then p = P + 2 is even
and ≥ 4, so not prime.

Checked here (core Lean): `two_never`, the parity step.
Not checked here: "primorial(k) is even for k ≥ 1" (it has the factor 2) and
the definition of the sequence.
-/

theorem two_never (p P : Nat) (hP : P % 2 = 0) (hP2 : 2 ≤ P) (h : p = P + 2) :
    2 ∣ p ∧ 2 < p := by
  subst h
  constructor
  · omega
  · omega

theorem primorials_even : (2 % 2 = 0) ∧ (6 % 2 = 0) ∧ (30 % 2 = 0) ∧ (210 % 2 = 0) := by decide
