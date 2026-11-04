# OEIS A104896: counting integers below 10^n with no digit 0, 1, 2

**Source.** [A104896](https://oeis.org/A104896) (a(0) = 0, a(n) = 7a(n−1) + 7), comment: "Conjecture: this is also
the number of integers from 0 to 10^n - 1 that lack 0, 1 and 2 as a digit." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** 0 has the digit 0; the others are strings of length 1..n over {3, …, 9}: 7 + 7² + … + 7^n,
which satisfies the recurrence.

**Evidence.**
- Lean: [`A104896.lean`](A104896.lean): a(n) = 7 + … + 7^n for all n and the direct count for n = 3.
  Outside Lean: the positional-notation bijection.
- `certificate/check.py`: direct count for n ≤ 6.
- Lean (Mathlib): [`A104896_mathlib.lean`](A104896_mathlib.lean), `A104896_main`: for every n, the number of x < 10^n whose decimal digits (Mathlib `Nat.digits`, with 0 written "0") all lie in {3, ..., 9} equals a(n) (the recurrence). Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).
**Prior art.** No source found; trivial count. [A104896](https://oeis.org/A104896) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
