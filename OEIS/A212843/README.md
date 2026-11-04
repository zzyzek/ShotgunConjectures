# OEIS A212843: Carmichael numbers with prime factors ≡ 1 (mod 10)

**Source.** OEIS [A212843](https://oeis.org/A212843), conjectures by Marius Coman (2012):
(1) "only Carmichael numbers of the form 10n+1 can have prime divisors of the form 10k+1";
(2) "all Carmichael numbers C (not only with three prime divisors) of the form 10n+1 that have
only prime divisors of the form 10k+1 can be written as C = (30a+1)*(30b+1)*(30c+1),
C = (30a+11)*(30b+11)*(30c+11), or C = (30a+1)*(30b+11)*(30c+11). In other words, there are no
numbers of the form C = (30a+1)*(30b+1)*(30c+11)." (OEIS text, CC BY-SA 4.0.)

**Reading.** "Not only with three prime divisors" means the three factors may be composite
(products of prime factors). The "in other words" sentence is not equivalent to (2) under this
reading, so it is treated separately.

**Result.**
- (1) True.
- (2) True: every such C can be written in one of the three listed forms.
- The "in other words" sentence is true for Carmichael numbers with exactly three prime factors
  and **false** in general: C = 1044430736441 = 41·191·281·521·911 (a Carmichael number, all five
  primes ≡ 11 mod 30) equals 7831 · 146401 · 911 with 7831 ≡ 146401 ≡ 1 and 911 ≡ 11 (mod 30).
  Four such C (five prime factors, all ≡ 11 mod 30) occur below 10^13.

**Argument.**
- (1) If a prime p ≡ 1 (mod 10) divides C, Korselt gives 10 | p - 1 | C - 1.
- Primes ≡ 1 (mod 10) are ≡ 1 or 11 (mod 30) (21 is excluded by 3), and products of such numbers
  stay in {1, 11} mod 30 (11^2 ≡ 1). A prime factor ≡ 1 (mod 30) gives 3 | p - 1 | C - 1, so
  C ≡ 1 (mod 3); since 11 ≡ 2 (mod 3), C then has an even number of prime factors ≡ 11 (mod 30)
  and C ≡ 1 (mod 30).
- (2) Group the prime factors into three nonempty blocks. If C ≡ 1 (mod 30), any grouping has an
  even number of blocks ≡ 11: forms (1,1,1) or (1,11,11). If C ≡ 11 (mod 30), all primes are
  ≡ 11 and their number r is odd ≥ 3; put one prime in each of two blocks and the rest (odd count)
  in the third: form (11,11,11).
- Three prime factors: (30a+1)(30b+1)(30c+11) with 30a+1 prime forces C ≡ 1 (mod 3), but the
  product is ≡ 2 (mod 3). With r ≥ 5 primes all ≡ 11 (mod 30) (r odd), pairing four of them gives
  the form (1,1,11); the example above is one.

**Evidence.**
- Lean (Mathlib): [`A212843_mathlib.lean`](A212843_mathlib.lean) proves the full result (`A212843_part1, A212843_part2, A212843_three, A212843_other_words_false`): (1) and (2) for all Carmichael numbers (factors > 1 in (2)), the 'in other words' sentence for three prime factors, and its failure at 1044430736441; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, `three_le_card_primeFactors`, Korselt sufficient direction for the witness. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A212843.lean`](A212843.lean): `part1`, `three_primes` ((30a+1)(30b+1)(30c+11) ≡ 2 mod 3
  for all a, b, c), and for C = 1044430736441 the factorisation, primality of the five factors
  (trial division), Korselt's condition p - 1 | C - 1, and the grouping. Outside Lean: Korselt's
  criterion (both directions; the sufficient one to call the example Carmichael).
- `certificate/psp_scan.py`: Feitsma–Galway base-2 pseudoprimes below 10^13 with factorisations
  ([`data/psp2-annot-below-1e13.txt`](../../DATA.md)): no exception to (1) among 18 699
  Carmichael numbers; four Carmichael numbers whose prime factors are five primes ≡ 11 (mod 30):
  1044430736441, 1894509409001, 3558903712001, 3596565792401.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A212843_mathlib.lean`](A212843_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A212843.lean`](A212843.lean) checks the parts named under Evidence. **Disputed in part:** the scan recorded the whole entry as
proved; its argument ("a factor 1 mod 30 forces 3 | C - 1") only applies to prime factors, and
the "in other words" sentence fails for composite factors.

**Prior art.** Partly known. [OEIS A212843](https://oeis.org/A212843) (fetched 2026-11-04) already notes (C. R. Greathouse IV, 2012) that the first conjecture follows from Korselt. The second conjecture and the failure of its 'in other words' restatement (C = 1044430736441) are not in the entry; history shows no later edits beyond a 2025 link fix. Searched: entry, OEIS cross-reference search, edit history. The counterexample is worth an OEIS comment. (Prior-art review 2026-11-04.)
