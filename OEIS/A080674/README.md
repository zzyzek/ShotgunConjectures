# OEIS A080674: counting integers below 10^n with digits only in {6,7,8,9}

**Source.** [A080674](https://oeis.org/A080674) (a(n) = (4/3)(4^n − 1)), comment by A. Wajnberg (2005):
"Conjectured to be the number of integers from 0 to (10^n)-1 that lack 0, 1, 2, 3, 4 and 5 as a digit."
(OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** 0 has the digit 0. A positive integer below 10^n with no digit in {0..5} is a string of
length k ∈ {1..n} over {6, 7, 8, 9}: 4^k of each length, total 4 + … + 4^n = (4/3)(4^n − 1).

**Evidence.**
- Lean: [`A080674.lean`](A080674.lean): the geometric sum for all n and the direct count for n = 3.
  Outside Lean: the positional-notation bijection.
- `certificate/check.py`: direct count for n ≤ 6.
- Lean (Mathlib): [`A080674_mathlib.lean`](A080674_mathlib.lean), `A080674_main`: for every n, the number of x < 10^n whose decimal digits (Mathlib `Nat.digits`, with 0 written "0") all lie in {6, 7, 8, 9} is 4(4^n - 1)/3. The positional-notation step is proved there; nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).
**Prior art.** No source found; trivial count. [A080674](https://oeis.org/A080674) still says "Conjectured". Searched OEIS entry, references and history. Checked 2026-11-04.
