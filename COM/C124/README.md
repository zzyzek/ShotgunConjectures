# Coman C124: 3-Carmichael numbers divisible by 5: p(q - 2^n) holds

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 124. Paraphrase: Every 3-Carmichael number C divisible by 5 is p(q - 2^n) with p a prime factor other than 5, q prime, n >= 1.

**Result.** True: the only 3-Carmichael numbers divisible by 5 are 1105, 2465, 10585, and 1105 = 13(89 - 2^2), 2465 = 17(149 - 2^2), 10585 = 29(367 - 2).

**Argument.** C = 5pq, p < q. Korselt: q - 1 | 5pq - 1 = 5p(q-1) + 5p - 1, so 5p - 1 = h(q-1) with h <= 4 (q - 1 >= p).
Then h(5q - 1) = 25(p-1) + 20 + 4h, and p - 1 | 5q - 1 gives p - 1 | 20 + 4h <= 36, so p <= 37. The finite
enumeration gives the three numbers (also the complete list in the data below 1e13).

**Evidence.**
- Lean (Mathlib): [`C124_mathlib.lean`](C124_mathlib.lean) proves the full result (`C124_main`): every Carmichael number with three prime factors divisible by 5 is 1105, 2465 or 10585, and is p(q - 2^n) with p | C, p != 5, q prime, n >= 1; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, squarefreeness, and a kernel enumeration. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C124.lean`](C124.lean) checks the key identity, the finite enumeration, primality of 89, 149, 367 and the representations. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's necessary condition (p | C Carmichael implies p - 1 | C - 1; needs a primitive root mod p); Korselt's criterion for the three numbers.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): enumeration and data; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C124_mathlib.lean`](C124_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C124.lean`](C124.lean) checks the parts named under Evidence.

**Prior art.** Verdict `partly-known` (immediate). The list of 3-Carmichael numbers divisible by 5 is classical; checking the p(q - 2^n) shape on those three is new and trivial. Sources: [OEIS A087788 (fetched 2026-11-04)](https://oeis.org/A087788): 3-Carmichael numbers; the three divisible by 5 (1105, 2465, 10585) are classical (finitely many 3-Carmichael numbers with a given prime factor, Beeger 1950). Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, Google: 3-Carmichael numbers divisible by 5, OEIS A087788 (2026-11-04).
