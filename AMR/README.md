# Problem lists linked from amathr.org

Open-problem lists linked from https://amathr.org/problems/ (Cooper, TOPP, Egres Open, Froberg et al. and others); ids AMR-<list>-<k>, statements paraphrased with the list named in each README.

12 entries: 2 resolved by this project, 9 answered elsewhere, 0 disputed or partial.

Of the 2 resolutions: 1 proved in full in Lean, 1 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 0 on paper only (re-derived by a second reader; 0 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Resolved by this project

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [aimmatrix-mr8](aimmatrix-mr8/) | disproved | minimum rank of strict powers of a tree is not strictly decreasing | [full proof](aimmatrix-mr8/aimmatrix_mr8_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [shapiro-11](shapiro-11/) | disproved | Forsgård–Shapiro real-zero bounds (Conjectures 8, 9, 10) fail | [witness](shapiro-11/shapiro_11.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [aimmatrix-en1](aimmatrix-en1/) | proved | E(G) = E(G - e) + 2 only for G = K2 | — | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [aimmatrix-en2](aimmatrix-en2/) | disproved | edge deletion changes the energy by exactly 2 | [full proof](aimmatrix-en2/aimmatrix_en2_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [cooper-38](cooper-38/) | proved | the Linial-Luria count of d-dimensional permutations is tight (Keevash) | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [egres-63](egres-63/) | answered | minimum k-way cut in hypergraphs for fixed k | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [egres-97](egres-97/) | answered | well-balanced orientations of hypergraphs | — | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [froberg-M](froberg-M/) | proved | finiteness of B\_{n,m} and B'\_{n,m} | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [shapiro-12](shapiro-12/) | disproved | Forsgård–Shapiro Conjecture 9 (c̃\_k parity bound) is false | [witness](shapiro-11/shapiro_11.lean) | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [shapiro-13](shapiro-13/) | disproved | Forsgård–Shapiro Conjecture 10 (c\_k parity bound) is false | [witness](shapiro-11/shapiro_11.lean) | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [topp-67](topp-67/) | answered | fair partitions of convex polygons into n convex pieces | — | known | [known-theorem](../methods/known-theorem/README.md) |

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

### [shapiro-11](shapiro-11/): Forsgård–Shapiro real-zero bounds (Conjectures 8, 9, 10) fail

**Source.** B. Shapiro, *Problems around polynomials: the good, the bad and the ugly*,
Arnold Math. J. 1 (2015), arXiv 1503.05295, Section 7, Conjectures 8, 9, 10 (Forsgård–Shapiro),
listed at https://amathr.org/problems/. For f = Σ a_k x^k of degree n with all a_k > 0:
- Conj 8 (shapiro-11): the number of real zeros of f is at most the number of corners of
  t ↦ max_k (log a_k + kt + log C(n,k)).
- Conj 9 (shapiro-12): with c̃_k = (k+1)a_k² − k a_{k−1}a_{k+1} (a_{−1} = a_{n+1} = 0), and
  k_1 < … < k_m the indices with c̃_k > 0, the number of real zeros is at most the number of
  parity changes in (k_i mod 2).
- Conj 10 (shapiro-13): the same with c_k = a_k² − a_{k−1}a_{k+1} ≥ 0.

**Reading.** Real zeros are counted as distinct points (the counterexample below has simple
zeros, so the count with multiplicity gives the same answer).

**Result.** All three are false. One polynomial refutes all three:

P(x) = (19x² − 94x + 163) · ∏_{j=0}^{21} (2D x + 2D + 2j − 23),  D = 10^5.

P has degree 24, positive coefficients, and the 22 distinct rational zeros
x_j = −1 − (2j − 23)/(2D). Its corner count is 21, and both parity counts are 20.

- Conj 9 and 10: known. Katkova, Shapiro, Vishnyakova (arXiv 2403.12200, Section 5) refute
  them with Q_15(x) = (x+1)^13 (19/360360 x² − 89/720720 x + 83/720720) and its primitives
  Q_n(x) = ∫_{−1}^x Q_{n−1}, whose real zeros are a single zero at −1 of multiplicity n − 2.
- Conj 8: new here. Katkova–Shapiro–Vishnyakova list it as Conjecture 1 and do not refute it.
  Their own family refutes it: Q_21 has 18 corners against 19 real zeros (with multiplicity),
  and Q_n has n − 3 corners for 24 ≤ n ≤ 39 (checked). The polynomial P above splits the
  22-fold zero of Q_24 = (x+1)^22 · (19x² − 94x + 163)/K into distinct zeros. That makes the
  counterexample hold for distinct zeros too.

**Argument.** The zeros are explicit linear factors. 19x² − 94x + 163 has no real zeros
(94² < 4·19·163). Corners: f_trop is the maximum of the affine functions log w_k + kt with
w_k = a_k C(24,k). Its corners are the edges of the upper hull of the points (k, log w_k).
Index j is a strict hull vertex iff w_i^{l−j} w_l^{j−i} < w_j^{l−i} for all i < j < l. Exact
integer arithmetic finds the vertices 0..16, 20..24 (22 vertices, 21 corners). The indices
with c_k ≥ 0 and those with c̃_k > 0 are also 0..16, 20..24. That list has 16 + 4 = 20
parity changes. In all three cases 22 > the bound.

Lean: [witness](shapiro-11/shapiro_11.lean).

### [aimmatrix-en1](aimmatrix-en1/): E(G) = E(G - e) + 2 only for G = K2

Lean: —.

### [aimmatrix-en2](aimmatrix-en2/): edge deletion changes the energy by exactly 2

**Source.** AIM workshop "Spectra of families of matrices described by graphs, digraphs and sign patterns" (Oct
2006), report "Open Questions" by I.-J. Kim and A. W. Wehe, section 3 (Energy of graphs). E(G) is the sum of the
absolute values of the adjacency eigenvalues. Q1: if e is an edge of a connected graph G with E(G) = E(G \ e) + 2,
must G = K2? Q2: is there a graph G with E(G \ e) = E(G) + 2 for some edge e?

**Result.** Q1: yes (known: Day and So 2007). Q2: no; for every graph G and edge e, E(G \ e) < E(G) + 2, and in fact
E(G \ e) = E(G) + 2 would force E(G \ e) <= E(G).

**Argument.** For a real symmetric X, E(X) = sum |lambda_i(X)| = max tr(W X) over symmetric W with operator norm
<= 1, attained at W = sign(X) (write X = sum lambda_i v_i v_i^T; then tr(W X) = sum lambda_i <v_i, W v_i> and
|<v_i, W v_i>| <= 1). Let A = A(G), e = uv, B = e_u e_v^T + e_v e_u^T, so A(G \ e) = A - B and E(B) = 2.

- *Q2.* Take W = sign(A - B). Then E(G \ e) = tr(W A) - 2 W_uv <= E(G) - 2 W_uv <= E(G) + 2. Equality needs
  W_uv = -1. Since (W^2)_uu = sum_j W_uj^2 <= 1, row u of W (and likewise row v) is zero except W_uv = W_vu = -1.
  Then in tr(W (A - B)) every term touching u or v vanishes (the only nonzero W entries there sit on the deleted
  edge), so E(G \ e) = tr(W_R A_R) with R = V \ {u, v}, A_R the adjacency matrix of the induced subgraph G[R] and
  W_R a contraction: E(G \ e) <= E(G[R]). Extending sign(A_R) by zeros gives a contraction W' with
  tr(W' A) = E(G[R]), so E(G[R]) <= E(G). Hence E(G \ e) <= E(G) < E(G) + 2, a contradiction.
- *Q1.* The same computation with W = sign(A) gives E(G) <= E(G \ e) + 2 with equality only if W_uv = 1 and rows u, v
  of W vanish elsewhere; Day and So (ELA 16, 2007) show that equality holds iff e is a component of G, so for
  connected G, G = K2.

Lean: [full proof](aimmatrix-en2/aimmatrix_en2_mathlib.lean).

### [cooper-38](cooper-38/): the Linial-Luria count of d-dimensional permutations is tight (Keevash)

**Source.** J. Cooper, Combinatorial Problems I Like (section Permutations), listed at
amathr.org/problems: is P(n,d) >= ((1+o(1)) n/e^d)^{n^d}, where P(n,d) is the number of
d-dimensional permutations of order n (0/1 arrays [n]^{d+1} with exactly one 1 on every
axis-parallel line; d = 1 permutation matrices, d = 2 Latin squares)?

**Result.** Yes, known. P. Keevash, The existence of designs II, arXiv:1802.05900 (2018),
Theorem 1.8: the number of r-dimensional permutations of order n is (n/e^r + o(n))^{n^r}.
The lower bound comes from Keevash's design method (random greedy almost-decomposition, then
completion; the paper says the details follow its earlier counting argument for designs and
are omitted); the upper bound is Linial-Luria, Combinatorica 34 (2014) 471-486. Since
(n/e^d + o(n)) = (1+o(1)) n/e^d for fixed d, this is exactly the asked bound.

**Argument.** Citation only. Keevash phrases Theorem 1.8 as the answer to the open problem of
Linial-Luria, which is the problem Cooper lists.

Lean: —.

### [egres-63](egres-63/): minimum k-way cut in hypergraphs for fixed k

**Source.** Egres Open (Egerváry Research Group problem list, http://lemon.cs.elte.hu/egres/open/, Wayback 2024 snapshot), listed at https://amathr.org/problems/. Paraphrase: give a polynomial algorithm for minimum k-way cut in capacitated hypergraphs for fixed k ≥ 4 (k = 2 and k = 3 were known: k = 3 by M. Xiao).

**Reading.** "Capacitated" means non-negative hyperedge costs; a k-way cut is a set of hyperedges whose removal leaves at least k components.

**Result.** Solved (yes). For every fixed k there is a deterministic polynomial algorithm, running in n^O(k)·m time (n vertices, m hyperedges), for non-negative hyperedge costs.

**Argument.** Not reproduced (literature result). Chandrasekaran and Chekuri recover the parts of an optimal k-partition from minimum (S,T)-terminal cuts over polynomially many terminal choices, by divide and conquer. Earlier, Chandrasekaran, Xu and Yu gave a randomized polynomial algorithm (random contraction of hyperedges).

Lean: —.

### [egres-97](egres-97/): well-balanced orientations of hypergraphs

**Source.** Egres Open (Egerváry Research Group problem list, http://lemon.cs.elte.hu/egres/open/Well-balanced_orientations_of_hypergraphs; the page is gone and the 2022-2024 Wayback snapshots return 404), listed at https://amathr.org/problems/. The title appears both in the solved and in the open list of the archived problem list. Paraphrase (from the title and from the citing paper): extend Nash-Williams' well-balanced orientation theorem (every graph has an orientation with λ_D(u, v) ≥ ⌊λ_G(u, v)/2⌋ for all u, v) to hypergraphs, or decide which hypergraphs have such an orientation.

**Reading.** A hypergraph is oriented by choosing a head in each hyperedge (the other vertices are tails; Frank-Király-Király). The page text is lost; the reading follows Hörsch and Szigeti, who cite this page as the source of the question.

**Result.** Answered negatively. No theorem of Nash-Williams type holds: some hypergraphs have no well-balanced orientation, and deciding whether a given hypergraph has one is NP-complete.

**Argument.** - Small example (ours, re-derived): H on {a, b, c} with two copies of the hyperedge {a, b, c}. Every pair u, v lies in both hyperedges, so λ_H(u, v) = 2, and a well-balanced orientation needs λ_D(u, v) ≥ 1 for every ordered pair. A vertex can only be entered through a hyperedge whose head it is; two heads among three vertices leave some vertex v with no entering hyperedge, so λ_D(u, v) = 0.
- NP-completeness: Hörsch and Szigeti, Theorem 6 (reduction from a satisfiability-type problem; not re-derived).

Lean: —.

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

### [shapiro-12](shapiro-12/): Forsgård–Shapiro Conjecture 9 (c̃_k parity bound) is false

Lean: [witness](shapiro-11/shapiro_11.lean).

### [shapiro-13](shapiro-13/): Forsgård–Shapiro Conjecture 10 (c_k parity bound) is false

Lean: [witness](shapiro-11/shapiro_11.lean).

### [topp-67](topp-67/): fair partitions of convex polygons into n convex pieces

**Source.** The Open Problems Project, Problem 67 (Demaine, Mitchell, O'Rourke; https://topp.openproblem.net/p67), listed at https://amathr.org/problems/. Paraphrase: can every convex polygon be partitioned into n convex pieces that all have the same area and the same perimeter, for every n? (Nandakumar and Ramana Rao.)

**Result.** Yes, for every n ≥ 2. The TOPP page (read 2026-11-06) still lists the problem as open, with n = 2, 3, 4 and prime powers n = p^k settled (Nandakumar-Ramana Rao; Bárány-Blagojević-Szűcs; Aronov-Hubard and Karasev 2010). The secondary questions on the page (deciding feasibility for a given polygon, minimising total cut length, higher dimensions for non-prime-power n) are not addressed here.

**Argument.** Not reproduced (literature result). Akopyan, Avvakumov and Karasev prove that every convex body in the plane, in particular every convex polygon, has a partition into m convex parts of equal area and equal perimeter for every integer m ≥ 2. The prime-power case uses an equivariant-topology (configuration space / Voronoi) argument; they extend it to all m by an inductive cutting scheme with a degree computation.

Lean: —.

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

