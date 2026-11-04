# Coman C055: The C054 shape fails for p = 30k + 11, q = 180k + 61

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 55. Paraphrase: Every Poulet number with prime factors p = 30k + 11 and q = 180k + 61 is 6p^3(6n+1) - p^2(66n+5) + 30pn, n >= 1.

**Result.** False: 30411201 = 3 * 101 * 167 * 601 (k = 3).

**Argument.** The polynomial is pq(n(q-1) + p) = 60701(600n + 101) for p = 101; its values for n >= 1 start at 42551401 > 30411201.

**Evidence.**
- Lean: [`C055.lean`](C055.lean) checks the Poulet property and that no n >= 1 works. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and failures below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new`. Counterexample 30411201 not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
