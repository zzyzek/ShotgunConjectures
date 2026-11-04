# OEIS A176494: an odd prime p with |2^m - p| composite for every m ≥ 1

**Source.** OEIS [A176494](https://oeis.org/A176494) (least m ≥ 1 with |2^m - prime(n)| prime),
conjecture by Vladimir Shevelev (2010): "For every odd prime p, the sequence {|2^n - p|} contains at
least one prime." (OEIS text, CC BY-SA 4.0.)

**Result.** False. p = 509203 is prime and |2^m - 509203| is composite for every m ≥ 1, so a(n)
does not exist for prime(n) = 509203.

**Argument.** Covering congruences (Erdős's covering {3, 5, 7, 13, 17, 241} of the exponents mod
24). With o = ord_q(2):

| q | o | class of m (2^m ≡ p mod q) |
|---|---|---|
| 3 | 2 | 0 |
| 5 | 4 | 3 |
| 7 | 3 | 1 |
| 13 | 12 | 5 |
| 17 | 8 | 1 |
| 241 | 24 | 21 |

The classes cover Z/24, so for every m some q divides 2^m - p. Since 2^18 + 241 < p < 2^19 - 241,
|2^m - p| ≥ 15085 > 241, so q is a proper factor. p is prime (no divisor up to 713, and
714^2 > p).

**Evidence.**
- [`A176494.lean`](A176494.lean): `p_prime` (trial division, `decide +kernel`) and
  `cover_divides`: for every m, some q of the cover divides |2^m - p| and 1 < q < |2^m - p|
  (core Lean, axioms propext and Quot.sound). Nothing outside Lean.
- `certificate/a176494_cover.py`: the CRT search over class choices that found p (least prime in
  the resulting progressions), plus direct checks for m ≤ 49.

**Review level.** `lean-proof`.

**Prior art.** Verdict known (OEIS status conjecture; searched 2026-11-04). 509203 is a known dual Riesel number and is prime, so it refutes the conjecture; OEIS does not record this. Sources: [OEIS A176494 (fetched 2026-11-04)](https://oeis.org/A176494): still says Conjecture: every odd prime p has a prime |2^n - p|; [Wikipedia, Riesel number, section Dual Riesel numbers](https://en.wikipedia.org/wiki/Riesel_number): dual Riesel numbers = odd k with |2^n - k| composite for all n; 509203 (prime) is conjectured the smallest, i.e. it is one; [H. Riesel (1956), covering set {3,5,7,13,17,241} for 509203](https://en.wikipedia.org/wiki/Riesel_number): the covering congruences, which transfer to 2^m - k by m -> -m. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; Google: 509203 |2^n - p| composite dual Riesel; Google: A176494 counterexample.
