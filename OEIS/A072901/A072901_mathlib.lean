import Mathlib

/-
OEIS-A072901 (Mathlib). A072901: composite n such that the discriminant of Q(√n) is 4n.
Conjecture (V. Librandi, M. Marcus): all terms are squarefree. README result: true; trivial.

Reading: the discriminant of Q(√n) (n > 1 not a square) is the fundamental discriminant in
the square class of n (Q(√n) = Q(√D) for the fundamental discriminant D with D·n a square).
Since 4n·n = (2n)² is a square, "disc Q(√n) = 4n" is read as `Int.IsFundamentalDiscr (4n)`
(Mathlib's fundamental discriminants, `Mathlib.NumberTheory.FundamentalDiscriminant`).

Main theorem `A072901_main`: for every natural n (composite or not), if 4n is a fundamental
discriminant then n is squarefree and n ≡ 2 or 3 (mod 4); conversely those n give 4n
fundamental. Proof: Mathlib `Int.isFundamentalDiscr_four_mul`.

Outside Lean: the classical identification of the discriminant of the quadratic field
Q(√n) with the fundamental discriminant in the square class of n (needs the ring of integers
of a quadratic field, Z[√d] or Z[(1+√d)/2]; not in Mathlib). Mathlib's `NumberField.discr`
of Q(√n) is not computed here.
-/

theorem A072901_main (n : ℕ) :
    Int.IsFundamentalDiscr (4 * (n : ℤ)) ↔ Squarefree n ∧ (n % 4 = 2 ∨ n % 4 = 3) := by
  rw [Int.isFundamentalDiscr_four_mul, Int.squarefree_natCast]
  exact and_congr_right (fun _ => by omega)

/-- The conjecture under the reading above: composite n with disc Q(√n) = 4n are squarefree. -/
theorem A072901_conjecture (n : ℕ) (_hn : 1 < n) (_hc : ¬ n.Prime)
    (hd : Int.IsFundamentalDiscr (4 * (n : ℤ))) : Squarefree n :=
  ((A072901_main n).mp hd).1
