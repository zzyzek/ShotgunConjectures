# Coman C086: The twin pair (3, 5) does not arise from a 2-Poulet number

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 86. Paraphrase: For every twin prime pair (q1, q2) there is a 2-Poulet number p1 p2 with q1 = p2 - p1 - 1, q2 = p2 - p1 + 1.

**Result.** False for (3, 5): no 2-Poulet number has p2 - p1 = 4.

**Argument.** For P = p(p+4): P - 1 = 4 (mod p - 1) and P - 1 = -4 (mod p + 3). Fermat gives ord_{p_i}(2) | gcd(p_i - 1, P - 1) | 4, so both primes divide 15 = 2^4 - 1, impossible for two primes 4 apart. (None below 1e13.)

**Evidence.**
- Lean (Mathlib): [`C086_mathlib.lean`](C086_mathlib.lean) proves the full result (`C086_no_gap4, C086_false`): no p(p+4) with both factors prime is a base-2 pseudoprime, and the conjecture fails for (3, 5); Fermat + ord_p(2) | N - 1 (library `prime_dvd_pow_sub_one_of_gcd_dvd`). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C086.lean`](C086.lean) checks the two identities and 2^4 - 1 = 3 * 5. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Fermat's little theorem / ord_p(2) | p - 1.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): 2-Poulet numbers with difference 4 below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C086_mathlib.lean`](C086_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C086.lean`](C086.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Short order argument; not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
