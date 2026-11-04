# Coman C138: Primes p with p^2 = n(P - 1) + 1

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 138. Paraphrase: For every Poulet number P there are infinitely many primes p = sqrt(n(P-1) + 1), n >= 1.

**Result.** True.

**Argument.** Any prime p = 1 (mod P - 1), p > 1, works: p = (P-1)t + 1 gives p^2 = n(P-1) + 1 with n = t((P-1)t + 2). There are infinitely many such primes (Dirichlet; elementary for the residue 1).

**Evidence.**
- Lean: [`C138.lean`](C138.lean) checks the identity. Core Lean, no Mathlib, no `native_decide`.
- Lean (Mathlib): [`C138_mathlib.lean`](C138_mathlib.lean) proves the full statement, `C138_main`: for every P with `Nat.FermatPsp P 2` the set of primes p with p^2 = n(P - 1) + 1, n >= 1, is infinite (via Mathlib's `Nat.infinite_setOfPred_prime_modEq_one`).
- Outside Lean: none.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): examples; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C138_mathlib.lean`](C138_mathlib.lean)); the core-Lean file checks the identity only.

**Prior art.** Verdict `new` (immediate). Dirichlet for the residue 1 mod P-1. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
