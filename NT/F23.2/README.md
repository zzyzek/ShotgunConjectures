# Guy F23: n! = 2^a + 2^b only for n = 2, 3, 4

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section F23. Erdős "observes that n! = 2^a + 2^b only when n = 1, 2, 3, 4
and 5" (the operator sign is as printed in our copy; it may be an OCR loss of ±).

**Result.** The statement is an observation, not an open problem, and as printed its list is
slightly off.
- "+" reading: the solutions are exactly n = 2, 3, 4 (2 = 1 + 1, 6 = 4 + 2, 24 = 16 + 8);
  1 < 2 ≤ 2^a + 2^b and 120 = 1111000₂ has four binary ones. So "only when n ≤ 5" is true,
  but n = 1 and n = 5 are not solutions.
- "−" reading, n! = 2^a − 2^b: the solutions are exactly n = 1, …, 5 (1 = 2 − 1, 2 = 4 − 2,
  6 = 8 − 2, 24 = 32 − 8, 120 = 128 − 8). This matches the printed list, so it is the likely
  intended statement (or "±").

**Argument.**
- "+": 2^a mod 7 ∈ {1, 2, 4}, so 2^a + 2^b mod 7 ∈ {1, 2, 3, 4, 5, 6}, never 0, while 7 | n!
  for n ≥ 7. n ≤ 6 by inspection.
- "−": n! = 2^b(2^c − 1) with 2^b the 2-part of n!. For n ≥ 15, v₃(n!) ≥ ⌊n/3⌋, and 2^c − 1
  divisible by 3 forces c even, with v₃(2^c − 1) = 1 + v₃(c) (lifting the exponent for
  4^(c/2) − 1). So c ≥ 3^(⌊n/3⌋−1), while 2^c ≤ n! + 1 gives c ≤ n·log₂ n + 1;
  3^(⌊n/3⌋−1) > n log₂ n + 1 for n ≥ 15. For n ≤ 40, direct check (`misc_check.py`): the binary
  expansion of n! is a block of ones followed by zeros only for n ≤ 5.
  (The scan's note treated only "+" and missed that n = 1, 5 fail there.)

**Evidence.**
- Lean: [`F23_2.lean`](F23_2.lean), `plus_solutions`: n! = 2^a + 2^b ⇒ n ∈ {2, 3, 4}, and
  `plus_examples` (core Lean; axioms propext, Quot.sound).
- Lean + Mathlib: [`F23_2_mathlib.lean`](F23_2_mathlib.lean), `F23_2_main`: for every n,
  (∃ a b, n! = 2^a + 2^b) ↔ n ∈ {2, 3, 4} and (∃ a b, n! = 2^a − 2^b) ↔ n ≤ 5 (ℕ subtraction; n = 0 is also a
  "−" solution, 0! = 2 − 1). The "−" part uses `padicValNat.pow_sub_pow` (lifting the exponent) for n ≥ 18
  and a finite check for 6 ≤ n ≤ 17. Outside Lean: nothing.
- `certificate/misc_check.py`: all solutions of both forms for n ≤ 40.

**Review level.** `lean-proof` for both readings ([`F23_2_mathlib.lean`](F23_2_mathlib.lean)).
**Prior art.** Erdős's remark as cited; not searched. 2026-11-01.
