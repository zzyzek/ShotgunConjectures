# OEIS A230496: a(n) > 0 for every n

**Source.** [A230496](https://oeis.org/A230496), V. Shevelev and P. J. C. Moses, Oct 21 2013: "a(n) is the
minimal odd odious k > 1, such that k^i, i=1,2,...,n, all are odious, or a(n)=0, if there is no such k."
Conjecture in the entry: "for all n, a(n) > 0." (Odious = odd number of 1s in binary; evil = even.)
OEIS text, CC BY-SA 4.0, checked 2026-11-07.

**Result.** True. For every n there is an odd k > 1 with k, k^2, ..., k^n all odious. Explicitly, with
2^t > n, k = 1 + 2^{M e_1} + ... + 2^{M e_{2^t}} works whenever the exponents are "generic" in the sense below.

**Argument.** Let r = 2^t > n and write s(x) for the binary digit sum.

1. *Generic blocks.* Put e_0 = 0 and choose positive integers e_1, ..., e_r such that for each i <= n the map
   beta -> sum_b beta_b e_b is injective on compositions beta = (beta_0, ..., beta_r) of i (for example
   e_b = (n+1)^b). Choose M with 2^M > (r+1)^n, so every multinomial coefficient C(i; beta) with i <= n is
   below 2^M. Let k = sum_{b=0}^{r} 2^{M e_b}. Then k is odd, k > 1, and s(k) = r + 1 is odd.
2. *Carry-free expansion.* By the multinomial theorem k^i = sum_beta C(i; beta) 2^{M sum_b beta_b e_b}. The
   exponents are distinct multiples of M and every coefficient is below 2^M, so the binary blocks do not overlap
   and s(k^i) = sum_beta s(C(i; beta)).
3. *Orbit count.* The cyclic shift sigma of the indices 1..r (fixing 0) has order r = 2^t and permutes the
   compositions of i, preserving C(i; beta). Every orbit has size dividing 2^t, so it has even size unless it is a
   single composition fixed by sigma, i.e. beta_1 = ... = beta_r = a. Then r a <= i <= n < r forces a = 0 and
   beta = (i, 0, ..., 0), with coefficient 1. Summing over orbits, s(k^i) = s(1) + (sum over orbits of even
   size of size * s(coefficient)) is odd.

So k^i is odious for 1 <= i <= n, hence a(n) <= k and a(n) > 0.

**Evidence.**
- [`certificate/witness.py`](certificate/witness.py) builds k for t = 1, 2, 3 (n = 1, 3, 7) with greedily chosen
  injective exponents and checks s(k^i) odd directly; output in
  [`certificate/witness.out`](certificate/witness.out) (for t = 3, k has 1 137 145 bits and exponents
  0, 1, 8, 57, 256, 1153, 4181, 14180, 47381 in units of M = 24).
- Lean: not written (`needs-mathlib`). A formal proof needs the multinomial theorem over Fin (r+1), the
  carry-free digit-sum additivity s(a + 2^M b) = s(a) + s(b) for a < 2^M, and the orbit-counting lemma for a
  2-group action.
- Outside Lean: the whole argument (steps 1-3), written out above.

**Remarks.** The same orbit count shows that for generic sparse k (positive blocks, carry-free powers), the
parities of s(k), ..., s(k^n) equal those of the part of k fixed by the symmetry; this is why the construction
does not transfer to the evil/odious variants [A230497](https://oeis.org/A230497) and
[A230498](https://oeis.org/A230498), which remain open (see the scan's work/OEIS-A230496/REPORT.md).

**Review level.** `rechecked` (argument re-derived; explicit witnesses checked for n = 1, 3, 7).

**Prior art.** Checked 2026-11-07: the OEIS entries A230496-A230500 (conjecture still stated, no proof), web
search for "odious powers" and Shevelev's SeqFan post "Odious-evil stability" (2013), google-deepmind/
formal-conjectures (no entry found). No proof found.
