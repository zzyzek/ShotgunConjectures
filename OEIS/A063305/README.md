# OEIS A063305: newform dimension formula for Gamma_1(32) (18n is missing the constant -41)

**Source.** OEIS wiki, Talk:Conjectures/List, line for A063305: "Conjecture: a(n) = 18n".
[A063305](https://oeis.org/A063305) is "Dimension of the space of weight n cuspidal newforms for Gamma_1(32)",
offset 2, data -1, 13, 31, 49, 67, ... The entry itself now states: a(n) = 18*n - 41 for n > 2 (P. Luschny, Mar 04 2012).

**Reading.** The OEIS data are shifted by one weight: term a(n) is the dimension in weight n - 1
(a(3) is the weight-2 dimension; a(2) = -1 is not a dimension, the true weight-1 dimension is 0).
Below, n is the OEIS index and k = n - 1 the weight.

**Result.** Misstated. 18n differs from 18n - 41 by 41 at every n (e.g. a(3) = 13), and from the weight form by 23, so the printed formula is false for every n in either indexing. The constant -41 was dropped.
The corrected formula is true: a(n) = 18n - 41 for n >= 3 in the OEIS indexing, that is
dim S_k^new(Gamma_1(32)) = 18k - 23 for k >= 2.

**Argument.** The newspace dimension is a fixed finite combination of cusp-space dimensions:
from S_k(Gamma_1(N)) = sum over M | N and d | N/M of the images of S_k^new(Gamma_1(M)) under q -> q^d,
Moebius inversion gives dim S_k^new(Gamma_1(N)) = sum over M | N of beta(N/M) dim S_k(Gamma_1(M)),
with beta = mu * mu. For k >= 3 each dim S_k(Gamma_1(M)) (Cohen-Oesterle) is (k - 1)/12 times a
constant plus a term that depends only on k mod 12 (elliptic and irregular-cusp terms, present only
for M <= 4); the k = 2 term has an extra Eisenstein correction. G. Martin, J. Number Theory 112 (2005)
298-331, Theorem 13 (Gamma_1, k >= 2; Theorem 1 for Gamma_0) writes this out explicitly.
So for k >= 3, on each residue class of k mod 12, the true dimension is linear in k; the corrected
formula has the same shape. Two such functions agree for all k >= 3 once they agree for 24
consecutive k (two values per class). PARI/GP `mfdim([32, k, -1], 0)` agrees with the formula for
k = 2..80, which covers k = 2 and the 24 values k = 3..26.

**Evidence.**
- `certificate/newdim.gp` (PARI/GP, run `gp -q newdim.gp`): compares `mfdim` with the corrected formula
  in both indexings for k = 2..80 (all four levels 16, 32, 48, 64), compares the OEIS data with `mfdim`,
  and counts agreements of the printed formula (none); output in `certificate/newdim.log`.
- Lean: none. Dimensions of spaces of modular forms are not available in core Lean or Mathlib.
- Outside Lean: the dimension formula (Cohen-Oesterle / Martin Theorem 13) and PARI's `mfdim`.
  Martin's paper was not re-read for this write-up; the quasi-linear shape was re-derived from the
  Cohen-Oesterle formula as above.

**Review level.** `rechecked`: the corrected formula was recomputed against `mfdim` and the
reduction to finitely many weights re-derived.

**Prior art.** Verdict `misstated` (immediate). The corrected formula is printed in the entry
(see Source); its proof is the Cohen-Oesterle formula, written out by Martin. Sources:
[G. Martin, Dimensions of the spaces of cusp forms and newforms on Gamma_0(N) and Gamma_1(N),
J. Number Theory 112 (2005) 298-331, Thms 1 and 13](https://arxiv.org/abs/math/0306128);
[OEIS A063305](https://oeis.org/A063305) (fetched 2026-11-05). Searched: OEIS entry and history, arXiv,
google-deepmind/formal-conjectures (tree listing: no file for this A-number), 2026-11-05.
