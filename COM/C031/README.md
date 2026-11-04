# Coman C031: Poulet numbers with three or more factors: P = q((r+1)q - r) fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 31. Paraphrase: Every Poulet number with at least three prime factors has a prime factor q with P = q((r+1)q - r), r natural.

**Result.** False: 617093 = 43 * 113 * 127. 3352 failures below 1e13.

**Argument.** P/q must be r(q-1) + q, i.e. = 1 mod q - 1 and >= q; P/q mod (q-1) is 29, 85, 71 for q = 43, 113, 127.

**Evidence.**
- Lean: [`C031.lean`](C031.lean) checks 617093 is Poulet, its prime divisors are exactly 43, 113, 127 (Euclid's lemma), and the form fails for each. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and count; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `known` (immediate). Same counterexample already in the OEIS entry. Sources: [OEIS A215672 (fetched 2026-11-04)](https://oeis.org/A215672): 'The conjecture fails for a(80) = 617093 = 43*113*127' - Greathouse, Dec 07 2014. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A215672 (2026-11-04).
