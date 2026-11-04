# Coman C042: Carmichael numbers divisible by p and 2p - 1 (true, short)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 42. Paraphrase: A Carmichael number divisible by primes p and 2p - 1 equals p(2p-1)(n(2p-2) + p).

**Result.** True (trivial given Korselt).

**Argument.** Korselt: 2p - 2 | C - 1. With C = p(2p-1)m and 2p - 1 = 1, p^2 = 1 modulo 2(p-1) (p odd; p = 2 is impossible
since C is odd), pm = 1, so m = p (mod 2p - 2); the least positive such m is p, so m = n(2p-2) + p, n >= 0.
No failure among 3480 cases below 1e13.

**Evidence.**
- Lean (Mathlib): [`C042_mathlib.lean`](C042_mathlib.lean) proves the full result (`C042_main`): every Carmichael number divisible by primes p and 2p - 1 is p(2p-1)(n(2p-2)+p); Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd` and `Nat.IsCarmichael.odd`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C042.lean`](C042.lean) checks for odd p, p(2p-1)m = 1 (mod 2(p-1)) implies m = p (mod 2(p-1)). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's necessary condition (p | C Carmichael implies p - 1 | C - 1; needs a primitive root mod p).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): all cases below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C042_mathlib.lean`](C042_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C042.lean`](C042.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). One-line Korselt argument; A182207 still lists it as a conjecture. Sources: [OEIS A182207 (fetched 2026-11-04)](https://oeis.org/A182207): still states the conjecture; no proof. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A182207 (2026-11-04).
