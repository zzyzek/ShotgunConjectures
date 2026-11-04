# OEIS A215461: 2n is a prime plus an odd nonprime for every n > 5

**Source.** OEIS [A215461](https://oeis.org/A215461): number of ordered decompositions of 2n into
an odd prime and an odd nonprime (1 counts as nonprime). Conjecture: "a(n) is never zero for
n > 5, verified to 10^9." (OEIS text, CC BY-SA 4.0.)

**Result.** True (elementary).

**Argument.** 2n - 3, 2n - 5, 2n - 7 are three odd numbers with distinct residues mod 3, so one is
divisible by 3; for n > 5 it exceeds 3, so it is an odd nonprime, and its partner 3, 5 or 7 is
prime.

**Evidence.** [`A215461.lean`](A215461.lean): `witness` for every n > 5 (core Lean). Outside
Lean: only that a multiple of 3 larger than 3 is not prime.

**Review level.** `lean-proof`.

**Prior art.** New to OEIS, trivial. [OEIS A215461](https://oeis.org/A215461) (fetched 2026-11-04) still states the conjecture; no edits since 2015. Searched: entry, OEIS cross-reference search, edit history. The mod-3 argument is worth an OEIS comment. (Prior-art review 2026-11-04.)
