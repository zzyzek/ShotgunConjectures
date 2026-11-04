# Coman C136: Primes (n + d^k)/d: none for P = 561, d = 3

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 136. Paraphrase: For every Poulet number P = n + d with d a prime factor, there are infinitely many primes (n + d^k)/d.

**Result.** False: P = 561, d = 3 gives no prime at all.

**Argument.** (558 + 3^k)/3 = 186 + 3^(k-1): 187 = 11 * 17 for k = 1, a multiple of 3 above 3 for k >= 2. (Also no prime for (1105, 5), (1905, 5) for k < 12.)

**Evidence.**
- Lean: [`C136.lean`](C136.lean) checks 561 Poulet and no prime for every k >= 1. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): direct; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Direct computation for P = 561, d = 3. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
