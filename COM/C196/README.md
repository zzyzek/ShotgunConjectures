# Coman C196: Poulet numbers as 2m + n with primes in one class mod 30

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 196. Paraphrase: Every Poulet number not divisible by 5 is 2m + n (distinct primes in one class) with all primes in the same class 30k + 1, 30k + 3, 30k + 7 or 30k + 9.

**Reading.** Read literally (mod 30). The listed residues 1, 3, 7, 9 suggest last digits (mod 10); under that reading the claim holds for all 88 such Poulet numbers below 2e5 and is open.

**Result.** False as stated: such sums are 3r (mod 30), hence divisible by 3, and 341 is not.

**Argument.** Direct.

**Evidence.**
- Lean: [`../C195/C195.lean`](../C195/C195.lean) (shared with COM-C195) checks both residue lemmas and 341 Poulet, not divisible by 3 or 5 (shared file C195). Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- Python check shared with [COM-C195](../C195/certificate/check.py).

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Literal reading refuted by a mod-3 obstruction (immediate). Reading concern: the classes 30k+3 and 30k+9 contain at most the prime 3, so the book likely meant 10k+1, 10k+3, 10k+7, 10k+9 (as in C197, C198); under that reading the statement is a Lemoine/Goldbach-type claim our result does not settle. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement (2026-11-04).
