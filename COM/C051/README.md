# Coman C051: Poulet numbers divisible by 23 and 67 are 23*67*(66n + 23)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 51. Paraphrase: Every Poulet number divisible by 23 and 67 is 23*67*(n(67-1) + 23) with n >= 1 (also given as a polynomial in p = 23).

**Result.** True.

**Argument.** ord_67(2) = 66, so 66 | P - 1. With P = 1541m and 1541 = 23 (mod 66), 23^2 = 1 (mod 66) gives m = 23 (mod 66).
m = 23 would give P = 35443, which is not a psp (23^2 | P would need 23 to be a Wieferich prime). All 1249 cases
below 1e13 fit.

**Evidence.**
- Lean: [`C051.lean`](C051.lean) checks for every P > 1 with 2^(P-1) = 1 (mod P) divisible by 23 and 67, the stated shape; and the polynomial identity. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): all cases below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `partly-known` (immediate). The Carmichael version is proved in A182515; the Poulet version needs ord_67(2) = 66 instead of Korselt and is not stated. Sources: [OEIS A182515 (fetched 2026-11-04)](https://oeis.org/A182515): Carmichael version (C = 23*67*(66n+23)) proved: 'follows from Korselt's criterion: 67 | a(n) so a(n) = 1 (mod 66)' - Greathouse, Oct 02 2012. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A182515 (2026-11-04).
