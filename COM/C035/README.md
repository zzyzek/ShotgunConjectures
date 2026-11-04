# Coman C035: P = 8pn + p^2 for one prime factor implies all (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 35. Paraphrase: If a Poulet number is 8pn + p^2 for one of its prime factors p (n an integer), then the same holds for every prime factor.

**Result.** True and trivial: the condition is P = 1 (mod 8), independent of p.

**Argument.** P = pm. 8pn + p^2 = P with n an integer means m = p (mod 8). For odd p, multiplying by p (p^2 = 1 mod 8) turns this into P = 1 (mod 8), and back.

**Evidence.**
- Lean: [`C035.lean`](C035.lean) checks the equivalence m = p (mod 8) iff pm = 1 (mod 8) for odd p. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): exhaustive check for P, p < 4000; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `known` (immediate). Already proved in the OEIS entry. Sources: [OEIS A218483 (fetched 2026-11-04)](https://oeis.org/A218483): 'All three conjectures are true (obvious from new characterization)' - Greathouse, Dec 07 2014; entry renamed to psp = 1 (mod 8). Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A218483 (2026-11-04).
