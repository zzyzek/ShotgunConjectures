# OEIS A214620, A214621: proportion of terms up to 2^25 (partial)

**Source.** [A214620](https://oeis.org/A214620): n such that some m != n has the same least and greatest prime
factor and the same multiset of binary digits. [A214621](https://oeis.org/A214621): additionally the same
multiset of decimal digits. Conjecture in both: for some X, more than 50% of the integers above X are terms.
(OEIS text, CC BY-SA 4.0, cached entries, checked 2026-11-07.)

**Result (partial; the conjecture stays open).** Exact proportions of terms, all n < 2^25:
A214620 per block [2^(L-1), 2^L): 0.4998 at L = 17, 0.5220 (L = 18), 0.5422, 0.5621, 0.5790, 0.5950, 0.6096,
0.6237, 0.6362 (L = 25), increasing at every step from L = 7. A214621 per decade: 0.0028 ([10^3, 10^4)), 0.0039,
0.0069, 0.0112, 0.0180 ([10^7, 2^25)). The b-files stop at 10000 terms (about 2·10^4 for A214620).

**Argument.** n is a term iff its class under the key (bit length, popcount, [decimal digit multiset,] least prime
factor, greatest prime factor) has at least two members below the class's upper limit; all classes of n < 2^25
are complete because bit length (and decimal length) are part of the key and 2^25 is a block boundary (for
A214621 the decade [10^7, 2^25) is incomplete, so its last proportion is a lower bound on that window only).

**Evidence.**
- [`certificate/dens.c`](certificate/dens.c), output [`certificate/dens25.out`](certificate/dens25.out); the
  definition reproduces the 56 data terms of A214620 (checked separately with sympy).
- Lean: none. Outside Lean: the computation.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07: OEIS entries, formal-conjectures, oeis-lean-proofs: nothing beyond the b-files.
Obstruction analysis in the scan repo, work/OEIS-A214620/REPORT.md.
