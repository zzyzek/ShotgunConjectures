# OEIS A229910: primitive roots g with g + g⁻¹ primitive (proved); the finite-field version fails at q = 25, 121

**Source.** OEIS [A229910](https://oeis.org/A229910): a(n) = number of 0 < g < p = prime(n) with g
and g + g⁻¹ primitive roots mod p. Conjectures (Z.-W. Sun, 2013): "a(n) > 0 for all n > 6", i.e.
every prime p > 13 has such g; and "Let F be a finite field with |F| = q > 13. Then there is a
primitive root g of F ... such that g + g^{-1} is also a primitive root of F. If q > 61, then there
exists a primitive root g of F such that g - g^{-1} is also a primitive root of F."
(OEIS text, CC BY-SA 4.0.)

**Result.**
- Prime case: true, by Cohen, Oliveira e Silva, Sutherland, Trudgian, Corollary 2 (exceptions for
  g + g⁻¹ are q ∈ {2, 3, 4, 5, 7, 9, 13, 25, 121}; the primes among them are ≤ 13).
- Finite-field case: false as stated. q = 25 and q = 121 have no primitive g with g + g⁻¹
  primitive, and q = 121 > 61 has none with g - g⁻¹ primitive.

**Argument.** Prime case: the cited theorem (character sums plus a computer search). Field case:
exhaustive search in F_25 = F_5[√2] and F_121 = F_11[√2].

**Evidence.**
- [`A229910.lean`](A229910.lean): in F_25 and F_121 no primitive g has g + g⁻¹ or g - g⁻¹
  primitive (`decide +kernel`; primitivity by g^((q-1)/r) ≠ 1 for primes r | q-1). Outside Lean:
  the prime case (the cited theorem).
- `certificate/a229910_fields.py`: all prime powers q < 400; the exception sets are exactly
  {2,3,4,5,7,9,13,25,121} (+) and {2,3,4,5,9,13,25,61,121} (-), as in the paper.

**Review level.** `lean-witness` for the field counterexamples; prime case resolved by others
(literature, not re-derived).

**Prior art.** Known. [OEIS A229910](https://oeis.org/A229910) (fetched 2026-11-04) contains E. Rodríguez's Sep 2026 comment applying [Cohen, Oliveira e Silva, Sutherland, Trudgian (2018), Cor. 2](https://arxiv.org/abs/1711.06392): the prime case holds and the finite-field case fails at q = 25, 121. Searched: entry, OEIS cross-reference search, edit history. (Prior-art review 2026-11-04.)
