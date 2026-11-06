import OpenProblemsLib

/-
OEIS A214758 (Carmichael numbers divisible by a smaller Carmichael number).
Conjecture (Marius Coman, entry): a Carmichael number C1 can be written as
C1 = (C2 + C3)/2, with C2 and C3 Carmichael numbers, only if both C1 and C3
are divisible by C2.
Counterexample (Charles R Greathouse IV, entry, Dec 2014):
46657 = (29341 + 63973)/2, 46657 = 13*37*97, 29341 = 13*37*61,
63973 = 7*13*19*37, and neither 29341 nor 63973 divides 46657.

Main theorem `A214758_false`: the conjecture, with Mathlib's
`Nat.IsCarmichael` (Korselt via lib `isCarmichael_of_factors`), is false;
`no_divisor` also rules out the reading with the roles of C2 and C3 swapped.
Not checked in this file: minimality (certificate/search.py: 46657 is the
least C1 below 10^6 with such a triple).
-/

open OpenProblemsLib

namespace A214758

theorem c1 : Nat.IsCarmichael 46657 :=
  isCarmichael_of_factors 46657 [13, 37, 97] (by norm_num) (by decide) (by norm_num) (by decide)
    (by decide)

theorem c2 : Nat.IsCarmichael 29341 :=
  isCarmichael_of_factors 29341 [13, 37, 61] (by norm_num) (by decide) (by norm_num) (by decide)
    (by decide)

theorem c3 : Nat.IsCarmichael 63973 :=
  isCarmichael_of_factors 63973 [7, 13, 19, 37] (by norm_num) (by decide) (by norm_num)
    (by decide) (by decide)

theorem mid : 2 * 46657 = 29341 + 63973 := by norm_num

theorem no_divisor : ¬ 29341 ∣ 46657 ∧ ¬ 63973 ∣ 46657 := by decide

theorem A214758_false : ¬ ∀ C1 C2 C3 : ℕ, C1.IsCarmichael → C2.IsCarmichael → C3.IsCarmichael →
    2 * C1 = C2 + C3 → C2 ∣ C1 ∧ C2 ∣ C3 := by
  intro h
  exact no_divisor.1 (h 46657 29341 63973 c1 c2 c3 mid).1
