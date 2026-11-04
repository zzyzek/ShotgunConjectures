# Coman C022: p(2p-1) - 2kp is a base-(p-1) psp

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 22. Paraphrase: If p and 2p - 1 are prime and p > 3, then p(2p-1) - 2kp is a Fermat pseudoprime to base p - 1 for some natural k.

**Result.** True.

**Argument.** k = (p+1)/2 gives n = p(p-2), composite. p - 1 is -1 mod p and 1 mod p - 2, n - 1 is even, so (p-1)^(n-1) = 1 mod p and mod p - 2, hence mod n. Only p odd, p >= 5 is used.

**Evidence.**
- Lean: [`C022.lean`](C022.lean) checks for every odd p >= 5: the identity for n and (p-1)^(n-1) mod n = 1. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): all p < 10^4; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Same elementary argument as C021. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
