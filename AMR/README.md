# Problem lists linked from amathr.org

Open-problem lists linked from https://amathr.org/problems/ (Cooper, TOPP, Egres Open, Froberg et al. and others); ids AMR-<list>-<k>, statements paraphrased with the list named in each README.

3 entries: 1 resolved by this project, 1 answered elsewhere, 0 disputed or partial.

Of the 1 resolutions: 1 proved in full in Lean, 0 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 0 on paper only (re-derived by a second reader; 0 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Resolved by this project

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [aimmatrix-mr8](aimmatrix-mr8/) | disproved | minimum rank of strict powers of a tree is not strictly decreasing | [full proof](aimmatrix-mr8/aimmatrix_mr8_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [lean-certificate](../methods/lean-certificate/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [froberg-M](froberg-M/) | proved | finiteness of B\_{n,m} and B'\_{n,m} | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |

## Weaker results on open problems (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [froberg-P](froberg-P/) | partial | order of ψ(f) = Σ\_a f(a) x^a on polynomials of degree < p | [witness](froberg-P/froberg_P.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

### [aimmatrix-mr8](aimmatrix-mr8/): minimum rank of strict powers of a tree is not strictly decreasing

**Source.** I.-J. Kim, A. W. Wehe, *Open Questions*, AIM workshop "Spectra of families of
matrices described by graphs, digraphs and sign patterns" (Palo Alto, October 2006; report dated
2007-09-03, aimath.org/WWN/matrixspectrum/matrixspectrum.pdf), question Q8, listed via
https://amathr.org/problems/. Paraphrase: the j-th power G^j has an edge uv (u ≠ v) when G has a
walk of length j between u and v. Q8 asks whether, for every tree T other than the star
K_{1,n−1}, the sequence mr(T), mr(T^2), … decreases strictly until it hits 2. Here mr(G) is the
least rank of a real symmetric matrix whose off-diagonal entry (u,v) is nonzero exactly when uv
is an edge (diagonal entries free).

**Reading.** The source defines the power by walks of length exactly j (the "strict power"
T^(j) of DeAlba et al. 2012). That is the reading used here. For a tree, uv is an edge of T^(j)
iff dist(u,v) ≤ j and dist(u,v) ≡ j (mod 2). (With ordinary powers, walks of length ≤ j, the
sequence ends at mr(K_n) = 1, so "hits 2" would not fit.)

**Result.** No. Let T be the path 0-1-2-3-4 with two extra leaves 5 and 6 attached at 4
(7 vertices, not a star). Then mr(T) = 5, mr(T^2) = 4, mr(T^3) = 4 and mr(T^4) = 2, so the
sequence 5, 4, 4, 2, … is not strictly decreasing before it reaches 2. A scan of all non-star
trees with at most 11 vertices found four more counterexamples with 8 vertices, all of the
same kind (mr(T^3) = mr(T^2) = 4), and no tree with mr(T^(j+1)) > mr(T^(j)) > 2 that our bounds
could certify.

**Argument.** Edge sets: T^2 = {02, 24} ∪ {13, 35, 36, 56} (a path on {0,2,4} and a paw on
{1,3,5,6}); T^3 = {01, 03, 12, 14, 23, 25, 26, 34, 45, 46} (bipartite, 2 and 4 adjacent to all
of 1, 3, 5, 6; 0 adjacent to 1, 3).
- Upper bounds. T^2: Gram matrix of the vectors 0 ↦ e1, 2 ↦ e1+e2, 4 ↦ e2,
  1 ↦ e3, 3 ↦ e3+e4, 5 ↦ e4, 6 ↦ 2e4 in R^4; rank ≤ 4. T^3: Gram matrix of 1, 3, 5, 6 ↦ e1, e2,
  e3, e4 and 0 ↦ (1,1,0,0), 2 ↦ (1,−1,1,1), 4 ↦ (1,−1,−1,−1); rank ≤ 4. T: the matrix with
  diagonal (−1,−1,−1,0,−1,0,0) and 1 on the edges has rank 5.
- Lower bounds. For any matrix A with the pattern of T^3, the 4×4 submatrix with rows
  (2,0,1,5) and columns (6,3,0,2) is upper triangular: the positions below its diagonal are
  non-edges (and none is a diagonal entry of A), and its diagonal entries are A_26, A_03, A_10,
  A_52, which are edges. So rank A ≥ 4. The same with rows (2,0,3,1), columns (4,2,5,3) for
  T^2, and rows (1,2,3,4,5), columns (0,1,2,3,4) for T (rank ≥ 5).
- mr(T^4) = 2: T^4 is the disjoint union of the cliques on {0,2,4} and {1,3,5,6}, each of
  minimum rank 1. Not needed for the counterexample and not in Lean.

Lean: [full proof](aimmatrix-mr8/aimmatrix_mr8_mathlib.lean).

### [froberg-M](froberg-M/): finiteness of B_{n,m} and B'_{n,m}

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and
from the other pockets*, Arnold Math. J. 4 (2018), §4.2, Problem M (listed at
https://amathr.org/problems/), going back to M.-D. Choi, T.-Y. Lam, B. Reznick, *Real zeros of
positive semidefinite forms I*, Math. Z. 171 (1980) 1–26. Paraphrase: for a real form p of even
degree m in n variables, let Z(p) be its set of real projective zeros. B_{n,m} (resp. B'_{n,m}) is
the supremum of |Z(p)| over non-negative forms (resp. sums of squares of forms) with
|Z(p)| < ∞. Are B_{n,m} and B'_{n,m} finite?

**Reading.** Only finiteness is asked. The exact values (Conjecture 4.2, Problem N of the same
paper) remain open and are not addressed here.

**Result.** Yes, known. Both are finite, with
B'_{n,m} ≤ B_{n,m} ≤ ((m−1)^n − 1)/(m − 2) (m ≥ 4; B_{n,2} = 1), and also
B_{n,m} ≤ m(2m−1)^(n−1)/2. The problem paper itself quotes the first (eigenvector) bound
from Cartwright–Sturmfels (2013); the second follows from Milnor (1964). So the question was
already answered when it was listed.

**Argument.** 1. *Milnor route.* Let p ≥ 0 with Z(p) finite, |Z(p)| = k. On the unit sphere S, the set
   V = {x ∈ R^n : p(x) = 0, |x|² − 1 = 0} consists of the 2k points ±x_i, so each is a
   connected component of V. Milnor's theorem (J. Milnor, *On the Betti numbers of real
   varieties*, Proc. AMS 15 (1964) 275–280) bounds the sum of Betti numbers of a real
   algebraic set in R^n cut out by polynomials of degree ≤ d by d(2d−1)^(n−1); here d = m.
   Hence 2k ≤ m(2m−1)^(n−1). Non-negativity is not even used: this bounds the number of real
   projective zeros of any form with finitely many such zeros.
2. *Eigenvector route (the bound quoted in the problem paper).* Each ±x_i is a strict local
   minimum of p on S (value 0, and p > 0 nearby on S). Take disjoint closed balls B_i around the
   2k points and let δ > 0 be the minimum of p over S ∩ ∂B_i. Forms whose symmetric tensor has
   exactly N = ((m−1)^n − 1)/(m − 2) complex eigenvector classes form a dense (Zariski-open,
   non-empty) set (D. Cartwright, B. Sturmfels, *The number of eigenvalues of a tensor*, Linear
   Algebra Appl. 438 (2013) 942–952, for generic symmetric tensors of order m in n
   variables). Pick such f with
   sup_S |f − p| < δ/2. Then f restricted to S ∩ B_i attains its minimum in the interior, at a
   critical point of f|_S, i.e. ∇f(x) = λx: an eigenvector. The k projective points give k
   distinct eigenvector classes, so k ≤ N.
3. B'_{n,m} ≤ B_{n,m} since sums of squares are non-negative.

Lean: needs Mathlib.

### [froberg-P](froberg-P/): order of ψ(f) = Σ_a f(a) x^a on polynomials of degree < p

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and
from the other pockets*, Arnold Math. J. 4 (2018), §4.3, Problem P (listed at
https://amathr.org/problems/). Paraphrase: for a prime p let ψ map a polynomial f over F_p of
degree at most p − 1 to Σ_{a ∈ F_p} f(a) x^a (a read as an integer in 0..p−1). Find the least
i ≥ 1 with ψ^i = id. The paper reports 8, 124, 1368, 32129475 for p = 3, 5, 7, 11.

**Reading.** "Find" for a given p. The paper gives no formula and asks for none explicitly. This
entry gives a structural reduction, an algorithm, values for p ≤ 59, and Lean certificates for
the paper's four values (p ≤ 11). A closed formula in p is not obtained (see the end of **Result**).

**Result.** Partial.
1. In the basis 1, x, …, x^(p−1), ψ has matrix Ψ[a][j] = a^j (0^0 = 1). Row 0 is (1, 0, …, 0),
   so ψ keeps the constant term and the hyperplane W = {f : f(0) = 0} is ψ-invariant. On W
   (basis x, …, x^(p−1)) ψ has matrix N[a][j] = a^j, 1 ≤ a, j ≤ p − 1, and
   charpoly(Ψ) = (x − 1)·charpoly(N).
2. ord ψ = ord N when 1 is not an eigenvalue of N, and ord ψ divides p·ord N otherwise.
3. Let g be a primitive root mod p. N is conjugate to F·P_π, where F[k][m] = g^(km) is the
   discrete Fourier matrix of Z/(p−1) over F_p (F² = −R with R: m ↦ −m, so F⁴ = I) and P_π
   is the permutation matrix of π(k) = (g^k mod p) mod (p−1), the discrete exponential
   read modulo p − 1.
4. ord ψ = lcm over the irreducible factors h^e of the minimal polynomial of Ψ of
   ord(x mod h)·p^⌈log_p e⌉ (standard). This gives ord ψ for p ≤ 59 in seconds
   (`certificate/psi_order.out`), for example p = 13: 517735224944 = 2^4·7·17·61·157·28393,
   p = 17: 97123470850224, p = 19: 3235839149340.
5. Observed for all p ≤ 59: the minimal polynomial of Ψ equals its characteristic polynomial,
   and 1 is a double root only at p = 29 (where 29 divides ord ψ and ord ψ = 29·ord N).
   The factor degrees of charpoly(N) vary irregularly with p (p = 13: one irreducible factor
   of degree 12; p = 31: degrees 2, 3, 3, 3, 6, 6, 7).

Open: a closed formula for ord ψ. By item 3 it is the order of a DFT matrix composed with the
discrete-exponential permutation, and its factorisation pattern over F_p shows no regularity
up to p = 59. We do not claim that no formula exists.

**Argument.** 1. Ψ[0][j] = 0^j is 1 for j = 0 and 0 otherwise; Ψ[a][0] = 1. So in the ordered basis
   (1 | x, …, x^(p−1)), Ψ = [[1, 0], [𝟙, N]] with 𝟙 the all-ones column.
2. Ψ^i = [[1, 0], [S_i 𝟙, N^i]] with S_i = I + N + … + N^(i−1). If N^i = I and N − I is
   invertible, then S_i = (N^i − I)(N − I)^(−1) = 0, so Ψ^i = I; conversely Ψ^i = I gives
   N^i = I. If N^k = I then S_(pk) = S_k(I + N^k + … + N^((p−1)k)) = p·S_k = 0.
3. Write a = g^k (0 ≤ k ≤ p − 2) and r(j) = j mod (p − 1). Then N[g^k mod p][j] = F[k][r(j)],
   i.e. N = Q_E F Q_r with permutation matrices for k ↦ g^k mod p and j ↦ r(j); conjugating
   by Q_E gives F·(Q_r Q_E) and Q_r Q_E is the permutation k ↦ π(k).
   F²[m][m'] = Σ_k g^(k(m+m')) = (p − 1)[m + m' ≡ 0] = −R[m][m'].
4. Ψ is invertible (Vandermonde with distinct nodes). In F_p[x]/(minpoly) the order of x is
   the stated lcm (Chinese remainder theorem; a unipotent part of nilpotency index e has
   order p^⌈log_p e⌉).

Lean: [witness](froberg-P/froberg_P.lean).

