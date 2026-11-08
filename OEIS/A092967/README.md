# OEIS A092967: "a(n)-1 has prime(n)-1 divisors" fails from n = 4 on (except n = 7)

**Source.** [A092967](https://oeis.org/A092967) (offset 1): largest prime of the form s + 1 with s squarefree and the
prime divisors of s below n (Amarnath Murthy, 2004; terms by Ryan Propper). Comment: "Conjecture: a(n)-1 has
prime(n) -1 divisors." (OEIS text, CC BY-SA 4.0, checked 2026-11-07.)

**Reading.** The name says prime divisors "< n", but the data use "<= n": a(13) = 6007 = 2·3·7·11·13 + 1, and the
data agree with the "<= n" rule for n = 1..23 (certificate/check.py). Both readings are treated.

**Result.** The conjecture is false. Under the data reading it holds for n = 1, 2, 3, 7 and fails for every other
n, except possibly an index n with prime(n) a Fermat prime larger than 65537 (none is known). Under the name
reading it already fails at n = 2. Under both readings a(4) = 7 and τ(6) = 4 ≠ 6 = prime(4) - 1.

**Argument.** s is squarefree, so τ(a(n) - 1) = 2^ω(s) is a power of 2. prime(n) - 1 is a power of 2 only when
prime(n) is 2 or a Fermat prime: prime(n) ∈ {2, 3, 5, 17, 257, 65537, ...}, n ∈ {1, 2, 3, 7, 55, 6543, ...}.
Data reading: a(1) - 1 = 1, a(2) - 1 = 2, a(3) - 1 = 6, a(7) - 1 = 210 have 1, 2, 4, 16 divisors (= prime(n) - 1).
At n = 55 (prime 257): a(55) = 4655594068170006391, ω(a(55) - 1) = 15, so τ = 2^15 ≠ 256. At n = 6543
(prime 65537): s = 2 · (17 primes near 65537, listed in certificate/fermat.out) has s + 1 prime and exceeds every
product of at most 16 primes ≤ 65537, so ω(a(6543) - 1) ≥ 18 and τ ≥ 2^18 ≠ 65536.

**Evidence.**
- Lean (core): [`A092967.lean`](A092967.lean): `a4_eq` (a(4) = 7 from the subsets of {2, 3}), `tau_6`,
  `fourth_prime`, `A092967_conjecture_false_n4`; no axioms.
- [`certificate/check.py`](certificate/check.py): recomputes a(n) for n ≤ 23 under the "< n" rule; the data equal
  the "<= n" rule (shifted by one).
- [`certificate/fermat.gp`](certificate/fermat.gp), [`certificate/fermat.out`](certificate/fermat.out): a(55) by
  exhaustive search over the 2^16 subsets, and the n = 6543 witness (BPSW probable prime).
- Outside Lean: none for the counterexample n = 4. The statements for n = 55 and 6543 are script-only
  (probable primes); the "every other n" claim is the parity-of-τ argument above (paper).

**Review level.** `lean-witness`.

**Prior art.** Checked 2026-11-07: OEIS entry (conjecture unchanged), formal-conjectures, oeis-lean-proofs:
nothing found.
