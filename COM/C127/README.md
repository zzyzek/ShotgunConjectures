# Coman C127: (P + 5^m)/30 is composite or non-integral for every m, for infinitely many Poulet P with 5 | P, 3 ∤ P

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat
Pseudoprimes* (2013), Part one, conjecture 127. Paraphrase: every Poulet number P divisible by 5 and
not by 3 has some m >= 1 with (P + 5^m)/30 prime.

**Result.** False, non-constructively, if Larsen's preprint theorem holds. Every P = 19664845
(mod 50862630) makes (P + 5^m)/30 a non-integer for even m and composite for odd m, and this
progression contains infinitely many Carmichael numbers by D. Larsen, arXiv:2504.09056 (2025,
preprint, not refereed). No explicit P is known: no base-2 pseudoprime below 10^13 lies in the class.

**Argument.** The class is P = 0 (mod 5), 1 (mod 6), -5 (mod 31), -5^3 (mod 13), -5^5 (mod 7),
-5^9 (mod 601); M = 30 * 7 * 13 * 31 * 601 = 50862630.
- Even m: P = 1 and 5^m = 1 (mod 3), so 3 ∤ P + 5^m and (P + 5^m)/30 is not an integer.
- Odd m: 2, 3 and 5 divide P + 5^m. The orders of 5 are 3 mod 31, 4 mod 13, 6 mod 7 and 12 mod 601,
  so q | P + 5^m on m = 1 (mod 3) for 31, 3 (mod 4) for 13, 5 (mod 6) for 7, 9 (mod 12) for 601.
  The odd residues mod 12 are 1, 7 (31), 3, 11 (13), 5 (7) and 9 (601), so every odd m is covered.
  Each q is coprime to 30, so q divides (P + 5^m)/30, which is at least (19664845 + 5)/30 > 601.
- Poulet numbers in the class: gcd(19664845, M) = 5, lambda(5) = 4, h = gcd(4, M) = 2 divides
  19664845 - 1, gcd(5, 2 phi(5)) = 1, and 36 ∤ M, so the progression is Carmichael compatible in
  Larsen's sense (definition before his Theorem 1). His Theorem 1 gives infinitely many Carmichael
  numbers in it; Carmichael numbers are Poulet numbers, and these are divisible by 5 and not by 3.

**Evidence.**
- Lean: [`C127.lean`](C127.lean), core Lean, no Mathlib, no `native_decide`, axioms `propext` and
  `Quot.sound`. `cover_divides`: for every P = a (mod M) and odd m, some q in {7, 13, 31, 601}
  divides (P + 5^m)/30 with 1 < q < (P + 5^m)/30. `even_not_int`: 30 ∤ P + 5^m for even m.
  `class_facts`: 5 | a, a = 1 (mod 3), a odd, gcd(a, M) = 5.
- `certificate/check.py` (standard-library Python): covering data, orders, Carmichael compatibility,
  a direct check for m < 2000 on three members of the class, and a scan of
  [`data/psp2-annot-below-1e13.txt`](../../DATA.md) (no psp2 below 10^13 in the class);
  output in `certificate/check.log`.
- Outside Lean: Larsen's theorem (arXiv:2504.09056, Theorem 1; preprint, not refereed) and that
  Carmichael numbers are Poulet numbers (proved in core Lean in [`../C128/C128.lean`](../C128/C128.lean),
  `carmichael_poulet`, not repeated here).

**Review level.** `lean-witness`: the covering is checked in core Lean for every P in the class and
every m; the existence of Poulet numbers in the class rests on Larsen's preprint.

**Prior art.** Verdict `partly-known`. The method is Erdos-type covering plus Larsen's theorem, as in
[COM/C128](../C128/README.md); this progression and the disproof of C127 were not found stated.
Sources: [D. Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056v2
(Oct 2025, preprint, no journal reference), Theorem 1](https://arxiv.org/abs/2504.09056): infinitely
many Carmichael numbers in every Carmichael-compatible progression; does not mention Coman.
Searched: Coman's OEIS entries, google-deepmind/formal-conjectures (tree listing: no Coman file),
the scan's tier-3 literature pass (2026-11-05).
