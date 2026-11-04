# Coman C027: n^E = n (mod 544) fails for the Euler pseudoprime 561

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 27. Paraphrase: n^E = n (mod 544) for every natural n and every Euler pseudoprime E.

**Result.** False: n = 2, E = 561 gives 2^561 = 512 (mod 544).

**Argument.** 561 is composite and 2^280 = 1 (mod 561), equal to the Jacobi symbol (2/561) = 1 (561 = 1 mod 8), so 561 is an Euler pseudoprime to base 2.

**Evidence.**
- Lean: [`C027.lean`](C027.lean) checks compositeness, 2^280 mod 561 = 1, 561 mod 8 = 1, 2^561 mod 544 = 512. Core Lean, no Mathlib, no `native_decide`.
- Lean (Mathlib): [`C027_mathlib.lean`](C027_mathlib.lean) proves `C027_main`: 561 is an Euler pseudoprime to base 2 (odd, composite, coprime to 2, 2^280 ≡ J(2 | 561) (mod 561) with Mathlib's `jacobiSym`; J(2 | 561) = 1 by Mathlib's second supplementary law `jacobiSym.at_two`), 2^561 % 544 = 512, so the conjecture is false. Outside Lean: nothing.
- Outside the core-Lean file: the value of the Jacobi symbol (2/561) (now proved in `C027_mathlib.lean`); nothing under the weaker definition 2^((E-1)/2) = +-1
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the disproof is proved in Lean + Mathlib ([`C027_mathlib.lean`](C027_mathlib.lean)), including the Jacobi symbol value the core-Lean file left outside.

**Prior art.** Verdict `new` (immediate). Direct computation 2^561 mod 544. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
