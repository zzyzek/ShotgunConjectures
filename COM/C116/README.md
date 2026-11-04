# Coman C116: Only two Carmichael numbers p^4 + 60p

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 116. Paraphrase: There are infinitely many Carmichael numbers p^4 + 60p with p prime (2821 and 29341 for p = 7, 13).

**Result.** False: these two are the only ones.

**Argument.** p | C, so Korselt gives p - 1 | C - 1 = (p-1)(p^3 + p^2 + p + 61) + 60, i.e. p - 1 | 60: p in {2, 3, 5, 7, 11, 13, 31, 61}. Only p = 7, 13 give Carmichael numbers.

**Evidence.**
- Lean (Mathlib): [`C116_mathlib.lean`](C116_mathlib.lean) proves the full result (`C116_main, C116_false`): {p prime : p^4 + 60p Carmichael} = {7, 13}, hence not infinite; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, non-Carmichael by a base-7 `powMod`, Korselt for 2821 and 29341. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C116.lean`](C116.lean) checks the identity, the candidate list, non-Carmichael witnesses for p = 2, 3, 5, 11, 31, 61, 2821 Carmichael (all bases), Korselt data for 29341. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's necessary condition (p | C Carmichael implies p - 1 | C - 1; needs a primitive root mod p); Korselt's criterion for 29341.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): the eight candidates; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C116_mathlib.lean`](C116_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C116.lean`](C116.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Korselt gives p - 1 | 60; finite check; not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
