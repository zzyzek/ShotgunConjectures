# OEIS A126142: squares of the terms are 6k+1 (trivial)

**Source.** OEIS [A126142](https://oeis.org/A126142) (primes p whose square has a prime
digit sum), comment by Vincenzo Librandi (2009): "a(n)^2 is of the form 6*k+1."
(OEIS text, CC BY-SA 4.0.) The entry already adds (Berselli 2014) that this is trivially true.

**Result.** True (trivial). Every n with gcd(n, 6) = 1 has n^2 ≡ 1 (mod 24), hence
n^2 ≡ 1 (mod 6). All terms are primes ≥ 5 (a(1) = 5), so gcd(a(n), 6) = 1.

**Argument.** n odd and 3 ∤ n: n^2 ≡ 1 (mod 8) and n^2 ≡ 1 (mod 3); equivalently check the
eight residues mod 24 prime to 6.

**Evidence.** [`A126142.lean`](A126142.lean): `sq_mod_24` and `sq_form_6k1` for every n
(core Lean; residues mod 24 by `decide` plus `Nat.pow_mod`).
[`A126142_mathlib.lean`](A126142_mathlib.lean), `A126142_main`: every prime p whose square has a prime
`Nat.digits 10` sum has p^2 = 6k + 1 (p = 2, 3 are excluded by their digit sums 4, 9). Outside Lean: nothing.

**Review level.** `lean-proof`: the comment for every term, in [`A126142_mathlib.lean`](A126142_mathlib.lean).

**Prior art.** Verdict known, immediate (OEIS status resolved-in-entry; searched 2026-11-04). Already marked trivially true in the entry. Sources: [OEIS A126142 (fetched 2026-11-04)](https://oeis.org/A126142): Berselli (Jun 2014): 'This comment is trivially true'. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history.
