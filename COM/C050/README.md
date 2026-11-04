# Coman C050: Infinitely many base-3 psp (3^(4k+2) - 1)/8

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 50. Paraphrase: There are infinitely many base-3 Fermat pseudoprimes (3^(4k+2) - 1)/8.

**Result.** True.

**Argument.** (3^(4k+2) - 1)/8 = (9^p - 1)/(9 - 1) with p = 2k + 1. Cipolla's theorem with a = 3: for prime p not dividing 3 * 8, i.e. p >= 5, this is a base-3 psp.

**Evidence.**
- Lean (Mathlib): [`C050_mathlib.lean`](C050_mathlib.lean) proves the full result (`C050_main`): the set of base-3 Fermat pseudoprimes (3^(4k+2) - 1)/8 is infinite; Cipolla (library `cipolla`, Mathlib's proof made public). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C050.lean`](C050.lean) checks the rewriting 3^(4k+2) = 9^(2k+1) and instances k = 2, 3. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Cipolla's theorem; infinitude of primes.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): k < 40; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C050_mathlib.lean`](C050_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C050.lean`](C050.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** Verdict `known` (immediate). Already resolved in the OEIS entry; Cipolla 1904 with a = 3. Sources: [OEIS A217853 (fetched 2026-11-04)](https://oeis.org/A217853): 'It is true: for example, when 2k+1 is a prime number' - Bruno Berselli, Jan 22 2013; M. Cipolla, Sui numeri composti P che verificano la congruenza di Fermat, Annali di Matematica (3) 9 (1904) 139-160: (a^(2p)-1)/(a^2-1) is a base-a psp for primes p not dividing a(a^2-1). Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A217853 (2026-11-04).
