# OEIS A145878: polynomial formulas for T(r+k, k), r = 3..7 (previous conjectures)

**Source.** OEIS [A145878](https://oeis.org/A145878): T(n,k) = number of permutations of [n] with
k strong fixed points. Formulas T(3+k,k) = 3k+3, T(4+k,k) = (k+1)(k+28)/2, T(5+k,k) =
(k+1)(3k+77), T(6+k,k) = (k+1)(k^2+110k+2982)/6, T(7+k,k) = (k+1)(3k^2+235k+7352)/2, now marked
"previous conjectures" in the entry (McGinnis 2018, with the paper of Baren et al.).
(OEIS text, CC BY-SA 4.0.)

**Result.** True (resolved by others; re-derived here).

**Argument.** The k strong fixed points cut a permutation into k + 1 consecutive blocks, each a
permutation with no strong fixed point (empty blocks allowed). With c(m) = T(m,0) (A052186:
1, 0, 1, 3, 14, 77, 497, 3676), T(r+k, k) = sum over compositions of r into k+1 parts of the
product of c(parts). Since c(1) = 0, at most floor(r/2) parts are nonempty, so
T(r+k,k) = sum_j C(k+1, j) w_r(j) is a polynomial in k of degree ≤ floor(r/2) ≤ 3. Agreement at 4
values of k proves each formula. (Example r = 4: w(1) = 14, w(2) = c(2)^2 = 1, so
T = 14(k+1) + C(k+1,2) = (k+1)(k+28)/2.)

**Evidence.**
- [`A145878.lean`](A145878.lean): with c(m) for m ≤ 7 and McGinnis's recursion
  T(n,k) = sum_{i=1..n-k+1} T(n-i,k-1) T(i-1,0), the five formulas hold for 0 ≤ k ≤ 8 (`decide`).
  Outside Lean: the block decomposition (gives the recursion and the degree bound) and the values
  of A052186.
- `certificate/a145878.py`: T computed from n! and the recursion; formulas hold for k ≤ 60.

**Review level.** `lean-witness`.

**Prior art.** Proved in the literature as cited by the entry (T. Baren et al., link in A145878;
D. A. McGinnis, Oct 2018).
