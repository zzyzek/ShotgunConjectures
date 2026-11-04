# Coman C054: Poulet numbers divisible by 11 and 61 are 11*61*(60n + 11)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 54. Paraphrase: Every Poulet number divisible by 11 and 61 is 11*61*(n(61-1) + 11) with n >= 1 (also given as a polynomial in p = 11).

**Result.** True.

**Argument.** ord_61(2) = 60, so 60 | P - 1. With P = 671m and 671 = 11 (mod 60), 11^2 = 1 (mod 60) gives m = 11 (mod 60).
m = 11 would give P = 7381, which is not a psp (11^2 | P would need 11 to be a Wieferich prime). All 2718 cases
below 1e13 fit.

**Evidence.**
- Lean: [`C054.lean`](C054.lean) checks for every P > 1 with 2^(P-1) = 1 (mod P) divisible by 11 and 61, the stated shape; and the polynomial identity. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): all cases below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Same order argument as C051 (ord_61(2) = 60); not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries, OEIS search 'divisible by 11 and 61' (2026-11-04).
