# Guy B16: every gap occurs between consecutive squarefree numbers

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B16. With f₁ < f₂ < … the squarefree numbers, Panaitopol asks whether
for each positive integer k there is an n with f_(n+1) − f_n = k.

**Result.** Yes, for every k ≥ 1 (and for each k a positive proportion of integers m start
such a gap). The argument is elementary and very likely known.

**Argument.** Fix k ≥ 2 (k = 1: 1, 2). Choose distinct primes p₁, …, p_(k−1) and, by the
Chinese remainder theorem, a class c mod Q = ∏ p_i² with c + i ≡ 0 (mod p_i²) for 1 ≤ i < k.
For m ≡ c (mod Q) the numbers m + 1, …, m + k − 1 are not squarefree. It remains to find such m
with m and m + k squarefree. Write m = c + Qj. For p = p_i we have m ≡ −i and m + k ≡ k − i
(mod p_i²), both nonzero because 0 < i, k − i < k ≤ p_i², so p_i² divides neither. For any other
prime p, the conditions p² | m and p² | m + k each exclude one class of j mod p² (Q is invertible
mod p²). By the standard squarefree sieve the set of j avoiding all excluded classes has density
∏_(p ∉ {p_i}) (1 − 2/p²) > 0 (the tail p > z excludes O(J/z + √J) of j ≤ J). So such m exist,
and m, m + k are consecutive squarefree numbers.

**Evidence.** Hand proof above. No computation needed.
Lean (Mathlib): [`B16_7_mathlib.lean`](B16_7_mathlib.lean) proves `B16_7_gap` (for every k ≥ 1
there is m with m, m + k squarefree and m + 1, …, m + k − 1 not squarefree) and `B16_7_main`
(with f_n = `Nat.nth Squarefree n`, some n has f_(n+1) − f_n = k). The Lean proof replaces the
density sieve by a finite count: primes p_i > k, CRT, and Σ_q 1/q² ≤ 35/72 so fewer than J of the
j < J are excluded for J = 10000 (c + Q + k)². Outside Lean: the "positive proportion" remark
(not proved).

**Review level.** `lean-proof`: the existence result is proved in Lean + Mathlib (the
positive-proportion side remark is not).
**Prior art.** Partly known: the density of a gap g between consecutive squarefree numbers is given by an inclusion–exclusion formula from Mirsky's pattern densities and computed for g ≤ 56 in [Mossinghoff–Oliveira e Silva–Trudgian, arXiv 1912.04972](https://arxiv.org/abs/1912.04972); no source found states that every k occurs. Searched: web, Marmet arXiv 1210.3829, OEIS A076259/A020753/A020754. Routine CRT + sieve. 2026-11-04.
