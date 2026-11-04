# Coman C006: Poulet numbers p^2 + 81p + 3pq with p = 30k+13, q = 30k+41: only two

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 6. Paraphrase: There are infinitely many Poulet numbers p^2 + 81p + 3pq with p = 30k + 13 and q = 30k + 41 prime.

**Reading.** The same k is used for p and q (both of Coman's examples, (13, 41) and (43, 71), use one k), so q = p + 28.
With independent k the question stays open; this item does not address that reading.

**Result.** False under the same-k reading: the only such Poulet numbers are 2821 and 14491.

**Argument.** With q = p + 28, N = p(4p + 165) and N - 1 = (p-1)(4p + 169) + 168. Since p | N and 2^(N-1) = 1 (mod p),
ord_p(2) divides both p - 1 and N - 1, hence 168, so p | 2^168 - 1. Among the 17 prime factors of
2^168 - 1 only 13 and 43 are 13 mod 30; both give Poulet numbers (2821, 14491). Brute force over p < 10^6
agrees.

**Evidence.**
- Lean (Mathlib): [`C006_mathlib.lean`](C006_mathlib.lean) proves the full result (`C006_main, C006_false`): the set of base-2 pseudoprimes p^2 + 81p + 3pq (p = 30k+13, q = 30k+41 prime, same k) is exactly {2821, 14491}, hence finite; Fermat + ord_p(2) | N - 1 (library `prime_dvd_pow_sub_one_of_gcd_dvd`), prime factors of 2^168 - 1 by Pratt certificates. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C006.lean`](C006.lean) checks the identity N - 1 = (p-1)(4p+169) + 168, the factorization of 2^168 - 1 with certified primes, the candidate filter, and both Poulet numbers. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Fermat's little theorem / ord_p(2) | p - 1; unique factorization (p is one of the listed primes).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): factorization of 2^168 - 1, candidates, brute force p < 1e6; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C006_mathlib.lean`](C006_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C006.lean`](C006.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Finite list {2821, 14491} by a Fermat-divisibility argument; not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
