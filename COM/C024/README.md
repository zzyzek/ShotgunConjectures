# Coman C024: p(kp - k + 1) is not always a psp to bases kp - k and kp - k + 2

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 24. Paraphrase: For prime p > 3 and k > 1, n = p(kp - k + 1) is a Fermat pseudoprime to both bases kp - k and kp - k + 2.

**Result.** False: p = 5, k = 2 gives n = 45 and 10^44 = 10 (mod 45); p = 5, k = 5 gives n = 105 and 20^104 = 85 (mod 105).

**Argument.** A base sharing the factor p with n cannot satisfy b^(n-1) = 1. The bases are -k and 2 - k mod p, and
kp - k + 1 = 1 - k mod p; for p < 60, k < 30 the claim fails exactly when k = 0, 1 or 2 (mod p)
(the scan's 'true when p does not divide k' is incomplete; the claim is false either way).

**Evidence.**
- Lean: [`C024.lean`](C024.lean) checks both counterexamples. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): counterexamples and the failure pattern for p < 60, k < 30; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Base shares a factor with n; direct computation. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
