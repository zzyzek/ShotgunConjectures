# Coman C004: 3-Poulet numbers without a factor 23 mod 30 are not all of the stated shape

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 4. Paraphrase: Every 3-Poulet number with no prime factor = 23 (mod 30) can be written p((n+1)p - n)((m+1)p - m) or p(np - (n+1))(mp - (m+1)).

**Reading.** The printed formula collapses to p^3 (it reads (n+1)*p - n*p); the evident intent, matching the scan,
is P = p * X * Y with p a prime factor and X, Y both n(p-1) + p (n >= 0) or both n(p-1) - 1 (n >= 1),
i.e. X, Y both = 1 or both = -1 modulo p - 1.

**Result.** False. Counterexample 158369 = 29 * 43 * 127.

**Argument.** 158369 is a base-2 psp; its factors are 29, 13, 7 (mod 30). For p = 29, 43, 127 the cofactor
5461, 3683, 1247 has no factorization X * Y of the required kind (bounded divisor search). Below 1e13
there are 8344 such failures (the scan reported 8357, likely counting the few data entries above 1e13).

**Evidence.**
- Lean: [`C004.lean`](C004.lean) checks Poulet property, primality of the factors, residues, and the exhaustive factor-pair search for each p. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and count over the Feitsma-Galway list; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new`. Counterexample 158369 not found stated anywhere. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
