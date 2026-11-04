# CFG F3: order of magnitude of g_d(n), the largest n-distance set in R^d

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991, section F3. g_d(n) is the largest number of points in R^d determining at most
n distinct distances. Bannai, Bannai & Stanton and Blokhuis showed g_d(n) ≤ C(d + n, n); the book
asks whether "g_d(n) ~ d^n is the correct order of magnitude for large n" (our copy's wording).

**Reading.** Two readings, both trivial.
- d → ∞ with n fixed (the reading in which d^n is natural): yes, g_d(n) = Θ_n(d^n).
- n → ∞ with d fixed (literal "for large n"): no, since C(d + n, n) = C(n + d, d) is a
  polynomial of degree d in n, far below d^n.

**Result.** Trivial or misstated (see Reading).

**Argument.** Upper bound: C(d + n, n) ≤ (d + n)^n / n! = (1 + o(1)) d^n / n! as d → ∞. Lower
bound: the 0/1 vectors of length d + 1 with exactly n ones lie in the hyperplane Σx_i = n
(a copy of R^d), number C(d + 1, n) = (1 + o(1)) d^n / n!, and their pairwise distances are
√(2j), 1 ≤ j ≤ n, so at most n distances (for d + 1 ≥ 2n; otherwise use fewer ones). Hence
g_d(n) ≍ d^n / n! for fixed n.

**Evidence.** Hand argument (second reader). Lean status `none` (real-geometry statement; the
counting part is trivial).

**Review level.** `rechecked`.
**Prior art.** Known: [Erdős Problems #1089](https://www.erdosproblems.com/1089) records C(d+1, n−1) + 1 ≤ g_d(n) ≤ C(d+n−1, n−1) + 1 (its g_d(n) is ours shifted by one; upper bound Bannai–Bannai–Stanton 1983) and the limit 1/(n−1)! as d → ∞, i.e. our fixed-n reading; the weight-n 0/1 construction is the classical Johnson-scheme example. The page was read through search snippets (direct fetch refused). 2026-11-04.
