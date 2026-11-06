# Guy D16: least common product of m triples with one sum and one product, m = 2..11

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D16.
Schinzel showed that arbitrarily many triples of positive integers can share both their sum and
their product. Guy suggests asking, for each multiplicity m, for the least common sum and the least
common product, and quotes (via Mauldon) sum 118 and product 25200 for m = 4.

**Reading.** A triple is (a, b, c) with 1 ≤ a ≤ b ≤ c. For each m, p(m) is the least P such that
some m distinct triples all have product P and one common sum. This is the "at least m" reading
(P may carry more than m triples with that sum). The least-sum question is OEIS
[A103277](https://oeis.org/A103277) (computed there for m ≤ 18, "exactly m" reading); this entry
does the product question, which is not in OEIS.

**Result.** For m = 2..11 the least common product p(m), with the common sum S of the extremal
triples:

| m | p(m) | S |
|---|---|---|
| 2 | 36 | 13 |
| 3 | 1200 | 39 |
| 4 | 25200 | 137 |
| 5 | 83160 | 185 |
| 6 | 776160 | 485 |
| 7 | 1965600 | 511 |
| 8 | 15724800 | 1022 |
| 9 | 34927200 | 1287 |
| 10 | 279417600 | 2574 |
| 11 | 1437836400 | 4279 |

No P ≤ 1.5·10^9 has 12 triples with one sum, so 1.5·10^9 < p(12) ≤ 11502691200 (the product
attached to the least sum 8558 in [A103278](https://oeis.org/A103278)). In this range the
"exactly m" reading gives the same values: the least P carrying a sum class of exactly m triples
is p(m) for every m ≤ 11. The extremal sum agrees with A103277 except at m = 4 and m = 6, where
the least-sum solutions (sums 118 and 400) have the larger products 37800 and 846720. So the
product sequence starts 36, 1200, 25200, 83160, 776160, and is not A103278.

**Argument.** Exhaustive search. For every P ≤ 1.5·10^9, factor P by a segmented sieve, list all
triples a ≤ b ≤ c with abc = P (a over divisors with a³ ≤ P, b over divisors of P/a with
a ≤ b ≤ √(P/a)), sort them by a + b + c and take the longest run. P is skipped only when the
upper bound (τ₃(P) + 3τ(P) + 2)/6 on its number of triples is below every multiplicity still
unrecorded, so no record can be missed.

**Evidence.**
- Lean: [`D16_1.lean`](D16_1.lean), core Lean, kernel `decide`.
  `wit_2` … `wit_11`: the listed m triples are distinct, ordered, have product p(m) and sum S.
  `no_two_lt_36`: no P < 36 has two distinct triples with one sum (minimality for m = 2), via
  `mem_trip` (every triple with product below 1200 is in the enumerated list) and `two_0`.
  Axioms: the `wit_*`, `two_0`, `plOk_true` use none; the lemmas use propext and Quot.sound.
  Outside Lean: minimality for m ≥ 3. (A kernel check of m = 3, all P < 1200, ran out of the
  1 GB Lean memory cap and was dropped.)
- [`certificate/prodsearch.c`](certificate/prodsearch.c): the search, run as
  `prodsearch 1 20000000` and six ranges covering [20000001, 1500000000]; all seven runs printed
  their `DONE` line. Output in [`certificate/records.txt`](certificate/records.txt) (every new
  record with its triples). Each range of 2.5·10^8 took under 35 minutes wall-clock on a loaded machine.
- Independent rechecks: [`certificate/triples.c`](certificate/triples.c) (divisor-pair method,
  written earlier in the scan) gives the same p(m) for m ≤ 8 over P ≤ 2·10^7
  ([`certificate/triples_2e7.log`](certificate/triples_2e7.log));
  [`certificate/recheck_small.py`](certificate/recheck_small.py) (enumerates all a ≤ b ≤ c with
  abc ≤ X and counts per (product, sum)) gives the same for m ≤ 5 at X = 3·10^5. For m = 9, 10, 11
  the values agree with the products A103278(9..11), which come from the independent sum search;
  minimality for m = 9..11 rests on `prodsearch.c` alone.
- [`certificate/make_lean.py`](certificate/make_lean.py) writes the Lean file from `records.txt`.

**Review level.** `lean-witness` (witnesses and m = 2 minimality in Lean; minimality for
m = 3..11 by exhaustive C search, m ≤ 8 confirmed by a second program).

**Prior art.** Checked 2026-11-06. OEIS searches for 36,1200,25200 / 1200,25200,83160,776160 /
83160,776160,1965600 / 776160,1965600: no results. A103277 and A103278 cover the least-sum
question only. ProofWiki has p(4) = 25200 as a statement without a minimality proof and notes
that Mauldon's Monthly problem E2872 actually concerns five triples. Kelly, Schinzel (Serdica
1996) and Zhang–Cai (Math. Comp. 2013) prove existence for every m, with no tables of least
products; arXiv:2408.13867 (triples with equal products, elliptic curves) has no such table.
google-deepmind/formal-conjectures has no entry for D16 or A103277. Verdict: partly known
(p(4) = 25200 stated by Guy; the rest new).
