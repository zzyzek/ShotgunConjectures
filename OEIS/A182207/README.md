# OEIS A182207: Carmichael numbers divisible by p and 2p - 1 are p(2p-1)(n(2p-2)+p)

**Source.** OEIS [A182207](https://oeis.org/A182207), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by p and 2p-1 (where p and 2p-1 are prime numbers) can be written as C = p*(2p-1)*(n*(2p-2)+p)."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Carmichael numbers are odd, so p = 2r + 1, r ≥ 1, and 2p - 2 = 4r. Write C = p(2p-1) m. Korselt for the prime factor 2p - 1 gives 4r | C - 1. If p(2p-1)m - 1 = 4rc then m - p = 4r(pc - (4r^2+5r+2)m), so m ≡ p (mod 2p-2). As m > 0 and p < 2p - 2 + p, m = p + n(2p-2) with n ≥ 0 (in fact n ≥ 1, since m = p gives p^2 | C).

**Evidence.**
- Lean (Mathlib): [`A182207_mathlib.lean`](A182207_mathlib.lean) proves the full result (`A182207_main`): every Carmichael number divisible by primes p and 2p-1 is p(2p-1)(n(2p-2)+p); Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd` and `Nat.IsCarmichael.odd`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182207.lean`](A182207.lean): `cofactor`: for all integers r, m, 4r | (2r+1)(4r+1)m - 1 implies 4r | m - (2r+1) (explicit witness, grind). Outside Lean: Korselt's criterion (necessary direction),
  which needs Fermat's little theorem and a primitive root mod p.
- `certificate/korselt_residues.py`: scan of Pinch's list of all Carmichael numbers below 10^21
  ([`data/pinch/c21.gz`](../../DATA.md), 57 s). A182207 for p ∈ {3, 7, 19, 31, 37, 79, 97}: 2 297 253 cases below 10^21, no exception.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182207_mathlib.lean`](A182207_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182207.lean`](A182207.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** New to OEIS, but immediate from Korselt's criterion. [OEIS A182207](https://oeis.org/A182207) (fetched 2026-11-04) still presents it as a conjecture; its edit history shows only term insertions in Oct 2026. Sister entries (A182151, A182206, A182208, A182381, A182515) carry C. R. Greathouse IV's 2012 one-line Korselt proofs of the analogous statements; this one was missed. Worth an OEIS comment. (Prior-art review 2026-11-04.)
