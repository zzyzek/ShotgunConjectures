# Coman C029: Poulet p2 = (p1 - d)n + d fails for 561 and 341

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 29. Paraphrase: If a Poulet number p2 is divisible by d and a smaller 2-Poulet number p1 is divisible by d, then p2 = (p1 - d)n + d for a natural n.

**Result.** False: p2 = 561, d = 11, p1 = 341 = 11 * 31; 561 mod 330 = 231, not 11.

**Argument.** Direct computation.

**Evidence.**
- Lean: [`C029.lean`](C029.lean) checks 341 and 561 are Poulet, 11 | 561, and 561 != 330n + 11. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `known` (immediate). The statement is already disproved in A214305 with a different counterexample; ours (p1 = 341, d = 11, p2 = 561) is smaller and could be added. Sources: [OEIS A214305 (fetched 2026-11-04)](https://oeis.org/A214305): Eiver Rodriguez, Sep 22 2026: the formula p2 = (p1-d)n + d fails for p1 = 23377 = 97*241, p2 = 34945, d = 241. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A214305 (2026-11-04).
