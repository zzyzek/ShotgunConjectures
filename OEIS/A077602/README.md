# OEIS A077602: M(n,1) ~ A077596(n) · sqrt(πn/2) for the Moebius polynomials

**Source.** [A077602](https://oeis.org/A077602) (decimal expansion of lim M(n,1)/2^n = 1.5301914...). Comment:
"Conjecture: M(n,1) ~ A077596(n) * sqrt(Pi*n/2), where A077596(n) is the largest coefficient of the n-th
Moebius polynomial, M(n,x)." (OEIS text, CC BY-SA 4.0, read 2026-11-06.) M(1,x) = 1 and
M(n,x) = 1 + x Σ_{m<n} ⌊n/m⌋ M(m,x) ([A074586](https://oeis.org/A074586)); [A077596](https://oeis.org/A077596)(n)
is the coefficient of x^(k0), k0 = ⌈n/2⌉ − 1 (the entry calls it the largest coefficient).

**Result.** True, for both readings of A077596(n) (the coefficient of x^(k0), or the largest coefficient).
Equivalently A077596(n) ~ c 2^n/√n with c = L √(2/π) = 1.2209161..., L = lim M(n,1)/2^n (Kotesovec's
numerical constant in A077596).

**Argument.**
1. *Recurrence.* ⌊n/m⌋ − ⌊(n−1)/m⌋ = [m | n], so for n ≥ 2
   M(n) − M(n−1) = x M(n−1) + x Σ_{d|n, d<n} M(d), i.e. M(n) = (1+x) M(n−1) + G(n) with G(n) = x Σ_{d|n,d<n} M(d).
   Unrolling, M(n) = Σ_{j=1}^{n} (1+x)^(n−j) G(j) with G(1) = 1. Every G(j) has nonnegative coefficients
   and degree ≤ j/2; write g_j = G(j,1).
2. *Sizes.* M(n,1) = 2M(n−1,1) + g_n and g_n ≤ Σ_{d ≤ n/2} M(d,1); induction gives M(n,1) ≤ 3^n, hence
   g_j ≤ (3/2)·3^(j/2) and Σ_j g_j 2^(−j) converges geometrically (ratio √3/2). So
   M(n,1)/2^n = Σ_{j≤n} g_j 2^(−j) → L = Σ_j g_j 2^(−j) > 0.
3. *Coefficients.* [x^k] M(n) = Σ_j Σ_i [x^i]G(j) · C(n−j, k−i). Let B(m) = C(m, ⌊m/2⌋) ~ 2^m √(2/(πm)).
   Upper bound for every k: [x^k] M(n) ≤ Σ_j g_j B(n−j). Split at j = n/2: for j ≤ n/2,
   B(n−j)/(2^(n−j) √(2/(πn))) ≤ √2·(1 + o(1)), so dominated convergence gives
   Σ_{j≤n/2} g_j B(n−j) = (L + o(1)) 2^n √(2/(πn)); for j > n/2, Σ g_j 2^(n−j) ≤ 2^n·O((√3/2)^(n/2)) = o(2^n/√n).
   Lower bound at k0: for fixed J and j ≤ J, the indices k0 − i are (n−j)/2 + O(J), and C(m, m/2 + O(1)) ~ B(m);
   so [x^(k0)] M(n) ≥ (Σ_{j≤J} g_j 2^(−j) − o(1)) 2^n √(2/(πn)), then J → ∞.
   Hence [x^(k0)] M(n) ~ max_k [x^k] M(n) ~ L 2^n √(2/(πn)) ~ M(n,1)/√(πn/2).

**Evidence.**
- [`certificate/check.py`](certificate/check.py): the recurrence of step 1 exactly for n ≤ 400; the ratio
  M(n,1)/(A077596(n)√(πn/2)) is 1.00059, 1.00030, 1.00015, 1.00010, 1.000075 at n = 50, 100, 200, 300, 400
  (error about 0.03/n), and the coefficient of x^(k0) is the largest one at these n.
- Lean: none (`needs-mathlib`). Outside Lean: the whole argument (recurrence, size bound, central binomial
  asymptotics and the dominated-convergence step).

**Review level.** `rechecked` (argument derived here, numerics).

**Prior art.** Checked 2026-11-06: A077602, A077596, A074587 still state the asymptotics as conjecture or
numerical observation; web search found no proof; not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones).
