# OEIS A187011: det(|p_i − p_j|) over the first n primes

**Source.** [A187011](https://oeis.org/A187011) (offset 0, a(0) = 1), Zhi-Wei Sun, Aug 30 2013: "Determinant
of the n X n matrix with (i,j)-entry equal to |p_i-p_j|, where p_k denotes the k-th prime." Comment: "Conjecture:
(-1)^(n-1)*a(n) > 0 for all n > 1, and |a(n)|^{1/n} tends to the infinity." (OEIS text, CC BY-SA 4.0; still stated
on 2026-11-05, revision #19 of Aug 16 2026.)

**Result.** Both parts are true. For n ≥ 2,

a(n) = (−1)^(n−1) · 2^(n−2) · (p_n − 2) · ∏_{i<n} (p_{i+1} − p_i),

so the sign part is immediate. The growth part follows from this formula and a sieve upper bound for prime pairs.

**Argument.**

1. *Distance matrix of a path.* For x_1 < … < x_n (n ≥ 2) in an ordered commutative ring, let D = (|x_i − x_j|) and
   d_i = x_{i+1} − x_i. Subtract row i+1 from row i (i < n), then column j+1 from column j (j < n). That is U D Uᵀ with
   U = I − (superdiagonal), det U = 1. The result is the arrowhead matrix with diagonal −2d_1, …, −2d_{n−1}, last row and
   last column (d_1, …, d_{n−1}), corner 0. Adding half of each of the first n−1 columns to the last column (in Lean:
   multiply by V with last column (1, …, 1, 2), det V = 2) makes it lower triangular with diagonal −2d_1, …, −2d_{n−1},
   x_n − x_1. Hence 2 det D = (−2)^(n−1) (∏ d_i)(x_n − x_1), i.e.
   det D = (−1)^(n−1) 2^(n−2) (x_n − x_1) ∏ d_i. This is the path case of the Bapat–Kirkland–Neumann formula for
   weighted trees.
2. *Sign.* With x_i = p_i every factor x_n − x_1 = p_n − 2 and d_i is positive, so (−1)^(n−1) a(n) > 0 for n ≥ 2.
3. *Growth.* Let g_i = p_{i+1} − p_i. By step 1,
   log|a(n)| / n = ((n−2) log 2 + log(p_n − 2) + Σ_{i<n} log g_i) / n, so |a(n)|^(1/n) → ∞ iff the mean of log g_i over
   i < n tends to infinity. Fix H. A gap g_i ≤ H means p_i and p_i + h are both prime for some even h ≤ H (or i = 1).
   The Selberg (or Brun) upper bound #{p ≤ x : p + h prime} ≤ C ∏_{q | h}(1 + 1/q) · x / log² x, uniform in even
   h ≥ 2 (Halberstam–Richert, *Sieve Methods*, Thm 3.11), with ∏_{q|h}(1 + 1/q) ≤ σ(h)/h ≤ 1 + log h and
   p_n ≤ 2 n log n (Chebyshev-type bound), gives #{i < n : g_i ≤ H} ≤ C' H (1 + log H) n / log n = o(n). So at least
   (1 − o(1)) n gaps exceed H and liminf (1/n) Σ log g_i ≥ log H. H is arbitrary.

   Why a sieve is needed: Chebyshev bounds alone do not suffice. A set with π(x) ≍ x/log x in which a fraction
   1 − 1/log log n of the first n gaps equal 2 and the rest have size about log n · log log n has bounded mean log gap.
   AM–GM bounds the geometric mean of the gaps from above (by (p_n − 2)/(n − 1)), not from below. Excluding such
   clustering is exactly a Brun-type statement that p, p + h are rarely both prime.

**Evidence.**
- Lean (Mathlib): [`A187011_mathlib.lean`](A187011_mathlib.lean). `distMat n x` = (|x i − x j|)_{i,j<n}, `p i` =
  `Nat.nth Nat.Prime i` (p 0 = 2), `a n = (distMat n p).det` over ℤ. Theorems:
  `det_distMat`: StrictMono x → 2 ≤ n → det (distMat n x) = (−1)^(n−1) · 2^(n−2) · (x (n−1) − x 0) ·
  ∏_{i ∈ range (n−1)} (x (i+1) − x i), for any `CommRing` with `LinearOrder` and `IsStrictOrderedRing` (ℤ, ℚ, ℝ);
  `A187011_formula`: the same for a n; `A187011_sign`: 2 ≤ n → 0 < (−1)^(n−1) · a n.
  Axioms: propext, Classical.choice, Quot.sound. Checked with `tools/leancheck-mathlib.sh` (exit 0, no warnings).
- `certificate/check.py`: exact determinants (Bareiss) equal the closed form for the primes, n = 2..60, and for 200
  random increasing integer sequences; the entry's data a(1..22) agree; prints the mean log gap
  (2.07, 2.25, 2.40 at n = 10^4, 10^5, 10^6) and log|a(n)|/n (2.76, 2.94, 3.10). Runs in 2 s.
- Outside Lean: the growth part (step 3). It uses the uniform Selberg/Brun upper bound for prime pairs and
  p_n ≪ n log n. Mathlib has the abstract Λ² sieve (`Mathlib/NumberTheory/SelbergSieve.lean`) but not the bound
  for prime pairs.

**Review level.** `rechecked` (sign part and determinant formula `lean-proof`; growth part by hand from a textbook
sieve bound).

**Prior art.** Checked 2026-11-05. The determinant of the distance matrix of a weighted tree on n vertices is
(−1)^(n−1) 2^(n−2) (∏ w_e)(Σ w_e): R. B. Bapat, S. J. Kirkland, M. Neumann, *On distance matrices and Laplacians*,
Linear Algebra Appl. 401 (2005) 193–209; unweighted case R. L. Graham, H. O. Pollak (1971). A187011 is the weighted
path with weights the prime gaps, so the sign part is a direct corollary of a known theorem. No proof of the A187011
conjecture found by web search; the entry cites none. Not in google-deepmind/formal-conjectures (no
`FormalConjectures/OEIS/187011.lean`).
