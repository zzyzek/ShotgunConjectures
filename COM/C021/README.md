# Coman C021: p(2p+1) - 2kp is a base-(p+1) psp: true for odd p, false for p = 2

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 21. Paraphrase: If p and 2p + 1 are prime, then p(2p+1) - 2kp is a Fermat pseudoprime to base p + 1 for some natural k.

**Result.** True for every odd p (k = (p-1)/2, n = p(p+2)); false for p = 2.

**Argument.** For odd p, k = (p-1)/2 gives n = p(p+2). The base p + 1 is 1 mod p and -1 mod p + 2, and n - 1 is even,
so (p+1)^(n-1) = 1 modulo p and modulo p + 2, hence modulo n (coprime). Primality of 2p + 1 is not
needed. For p = 2 (2 and 5 prime) the candidates are n = 10, 6, 2 (k = 0, 1, 2): 3^9 = 3 (mod 10),
3^5 = 3 (mod 6), and 2 is prime, so no k works.

**Evidence.**
- Lean: [`C021.lean`](C021.lean) checks the odd case for every p (identity for n and the CRT argument) and the p = 2 failure. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): odd p < 10^4 and the p = 2 candidates; output in `certificate/check.log`.

**Second reader: disputed.** The scan reports 'proved' for all p; the literal statement fails at p = 2 (3^9 mod 10 = 3, 3^5 mod 6 = 3, n = 2 prime). True for odd p.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Base = 1 and -1 modulo the two factors; elementary, not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
