# OEIS A135499: equal digit sums at odd and even positions implies 11 | n (trivial)

**Source.** OEIS [A135499](https://oeis.org/A135499): numbers whose digit sum at odd positions
equals the digit sum at even positions. Conjecture (Mathar, 2008): "this is a subsequence of
A008593" (multiples of 11). (OEIS text, CC BY-SA 4.0.) The entry already records that it follows
from the divisibility rule for 11 (Seidov 2008, Andersen 2014).

**Result.** True (trivial).

**Argument.** Let f(n) = (sum of digits at even positions from the right, counting from 0) minus
(sum at odd positions). Since 10 ≡ -1 (mod 11), n ≡ f(n) (mod 11). Equal sums means f(n) = 0
(the choice of counting from the left or right only swaps the two sums).

**Evidence.** [`A135499.lean`](A135499.lean): `mod11` proves n ≡ f(n) (mod 11) for all n by
strong induction (n = 10q + r), and `subsequence` concludes 11 | n when f(n) = 0. Core Lean,
nothing outside.

**Review level.** `lean-proof`.

**Prior art.** Verdict known, immediate (OEIS status resolved-in-entry; searched 2026-11-04). Already settled in the entry. Sources: [OEIS A135499 (fetched 2026-11-04)](https://oeis.org/A135499): Seidov (2008) and Andersen (2014): subsequence of multiples of 11, trivially. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history.
