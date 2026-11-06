# Problem lists linked from amathr.org

Open-problem lists linked from https://amathr.org/problems/ (Cooper, TOPP, Egres Open, Froberg et al. and others); ids AMR-<list>-<k>, statements paraphrased with the list named in each README.

1 entries: 0 resolved by this project, 0 answered elsewhere, 0 disputed or partial.

Of the 0 resolutions: 0 proved in full in Lean, 0 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 0 on paper only (re-derived by a second reader; 0 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Weaker results on open problems (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [froberg-P](froberg-P/) | partial | order of ψ(f) = Σ\_a f(a) x^a on polynomials of degree < p | [witness](froberg-P/froberg_P.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

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

