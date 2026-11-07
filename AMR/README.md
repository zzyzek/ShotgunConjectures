# Problem lists linked from amathr.org

Open-problem lists linked from https://amathr.org/problems/ (Cooper, TOPP, Egres Open, Froberg et al. and others); ids AMR-<list>-<k>, statements paraphrased with the list named in each README.

20 entries: 2 resolved by this project, 12 answered elsewhere, 1 disputed or partial.

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
| [aimmatrix-mr5](aimmatrix-mr5/) | proved | the minimum rank of the complement of the Kneser graph is n − 2k + 2 | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [aimmatrix-sap7](aimmatrix-sap7/) | proved | potentially nilpotent full sign patterns are spectrally arbitrary | — | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [cooper-38](cooper-38/) | proved | the Linial-Luria count of d-dimensional permutations is tight (Keevash) | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [egres-63](egres-63/) | answered | minimum k-way cut in hypergraphs for fixed k | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [egres-97](egres-97/) | answered | well-balanced orientations of hypergraphs | — | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [froberg-M](froberg-M/) | proved | finiteness of B\_{n,m} and B'\_{n,m} | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [shapiro-3](shapiro-3/) | proved | a line restriction of N point-charge potentials has at most N local maxima | — | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [shapiro-12](shapiro-12/) | disproved | Forsgård–Shapiro Conjecture 9 (c̃\_k parity bound) is false | [witness](shapiro-11/shapiro_11.lean) | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [shapiro-13](shapiro-13/) | disproved | Forsgård–Shapiro Conjecture 10 (c\_k parity bound) is false | [witness](shapiro-11/shapiro_11.lean) | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [topp-67](topp-67/) | answered | fair partitions of convex polygons into n convex pieces | — | known | [known-theorem](../methods/known-theorem/README.md) |

## Disputed or only partly answered (not counted as resolutions)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [froberg-4.3](froberg-4.3/) | partial | two generic quadrics in the exterior algebra (even n proved elsewhere; odd n open) | — | partly-known | [known-theorem](../methods/known-theorem/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |

## Weaker results on open problems (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [aimmatrix-sap3](aimmatrix-sap3/) | partial | fewest nonzeros of an irreducible β-arbitrary pattern (partial) | — | new | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [froberg-H](froberg-H/) | partial | T\_{n,2,2} = S/(x\_1², …, x\_n²)² has the WLP for every n | needs Mathlib | new | [elementary-proof](../methods/elementary-proof/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [froberg-O](froberg-O/) | partial | periods of the zero-set map φ on F\_p[x]: period 6 occurs (partial) | [witness](froberg-O/froberg_O.lean) | new | [complete-table-scan](../methods/complete-table-scan/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [froberg-P](froberg-P/) | partial | order of ψ(f) = Σ\_a f(a) x^a on polynomials of degree < p | [witness](froberg-P/froberg_P.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [froberg-R](froberg-R/) | partial | explicit odd-degree forms with the Lundqvist–Nicklasson series (partial) | — | new | [parametric-family](../methods/parametric-family/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |

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

### [aimmatrix-mr5](aimmatrix-mr5/): the minimum rank of the complement of the Kneser graph is n − 2k + 2

**Source.** I.-J. Kim, A. W. Wehe, *Open Questions*, AIM workshop "Spectra of families of
matrices described by graphs, digraphs and sign patterns" (October 2006; report dated
2007-09-03), Section 1, question Q5, listed via https://amathr.org/problems/. Paraphrase: for the
graph on the k-subsets of an n-set, two subsets adjacent when they intersect (the complement of
the Kneser graph K(n, k)), the report notes n − 2k + 2 ≤ mr ≤ n − 1 for 1 < k ≤ n/2 and asks
whether the lower bound is sharp. mr is the least rank of a real symmetric matrix whose
off-diagonal entry (S, T) is nonzero exactly when S ∩ T ≠ ∅.

**Result.** Yes: mr = n − 2k + 2 for all 2 ≤ k ≤ n/2, over every infinite field (Hu and Tang,
2026).

**Argument.** (Hu–Tang, case s = 1 of their threshold result; upper bound re-derived here.) Take
distinct nodes t_1, …, t_n, put q_S(x) = Π_{i ∉ S} (x − t_i) (degree n − k) and
A[S, T] = L(q_S q_T), where L(h) = Σ_i h(t_i) / Π_{j≠i}(t_i − t_j) is the divided difference of
order n − 1. Since L kills polynomials of degree below n − 1, the bilinear form (p, q) ↦ L(pq) on
polynomials of degree ≤ n − k has a Hankel matrix that vanishes above the anti-diagonal
a + b = n − 1, so its rank is at most 2(n − k) − n + 2 = n − 2k + 2. If S ∩ T = ∅ every node is a
root of q_S q_T, so A[S, T] = 0; otherwise A[S, T] = Σ_{i ∈ S∩T} q_S(t_i) q_T(t_i) / Π_{j≠i}(t_i − t_j),
which is nonzero for generic nodes (Hu–Tang's generic nonvanishing step). The lower bound is the
report's.

Lean: —.

### [aimmatrix-sap7](aimmatrix-sap7/): potentially nilpotent full sign patterns are spectrally arbitrary

**Source.** I.-J. Kim, A. W. Wehe, *Open Questions*, AIM workshop "Spectra of families of
matrices described by graphs, digraphs and sign patterns" (October 2006; report dated
2007-09-03), Section 2, question Q7, listed via https://amathr.org/problems/. Paraphrase: a sign
pattern is full when it has no zero entries. (N1) asks for a diagonal entry + and a diagonal
entry −, (N2) for a 2-cycle with α_kl α_lk = −. Q7 asks whether a full sign pattern that allows a
nilpotent matrix and satisfies (N1), (N2) is necessarily spectrally arbitrary (or inertially
arbitrary).

**Result.** Yes. R. Pereira proved that every potentially nilpotent full sign pattern is spectrally
arbitrary (hence also inertially arbitrary). For full patterns, (N1) and (N2) follow from
potential nilpotence, so they are redundant in Q7.

**Argument.** (Re-derived here; the route is the nilpotent-Jacobian method.)
1. N1, N2 are implied. Let A be a nilpotent realization of a full pattern. Then tr A = 0 with all
   a_ii ≠ 0, so the diagonal has both signs (N1). Also tr(A²) = Σ a_ii² + 2 Σ_{i<j} a_ij a_ji = 0
   with Σ a_ii² > 0, so some a_ij a_ji < 0 (N2).
2. A regular nilpotent realization exists. The realizations of a full pattern form an open subset
   Q of the n×n real matrices. Every real nilpotent N is a limit of real nilpotents with a single
   Jordan block: write N = P J P⁻¹ with J in Jordan form (real, since all eigenvalues are 0); adding
   ε to the superdiagonal positions of J that join consecutive blocks gives a nilpotent matrix with
   one Jordan block, and P(J + εE)P⁻¹ → N. So Q contains a nilpotent N₀ with one Jordan block.
3. Submersion. The map χ: M_n(R) → R^n sending A to the coefficients of det(xI − A) has surjective
   differential at every nonderogatory matrix. At N₀ = J_n (after similarity) take the
   perturbations A(c) = J_n + Σ c_i E_{n,n+1−i} (last row); det(xI − A(c)) = x^n − c_1 x^{n−1} − … − c_n,
   so already these n directions give an invertible Jacobian.
4. Scaling. By the implicit function theorem, every monic polynomial close to x^n is the
   characteristic polynomial of some matrix in Q near N₀. For t > 0, tA has the same sign
   pattern and the coefficient of x^{n−i} is multiplied by t^i; every monic real polynomial is
   carried into this neighbourhood by such a scaling. So the pattern is spectrally arbitrary.

Lean: —.

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

### [shapiro-3](shapiro-3/): a line restriction of N point-charge potentials has at most N local maxima

**Source.** B. Shapiro, *Problems around polynomials: the good, the bad and the ugly…*, Arnold
Math. J. 1 (2015) (arXiv:1503.05295), Section 1, Conjecture 3 (credited to Gabrielov, Novikov,
Shapiro), listed via https://amathr.org/problems/. Paraphrase: for points (x_i, y_i) in the plane,
real charges ξ_i and α ≥ 1/2, the function Ψ(x) = Σ_{i=1}^N ξ_i ((x − x_i)² + y_i²)^{−α} has at most
N local maxima on the real line. The source notes it was open even for N = 3, α = 1, unit charges.

**Reading.** Ψ is taken smooth on R, that is y_i ≠ 0 (a charge with y_i = 0 makes Ψ singular at
x_i; for the singular case see the remark below). Charges with the same (x_i, |y_i|) are combined;
if all combined charges vanish, Ψ ≡ 0 and the statement is void (every point is a non-strict
local maximum); this degenerate case is excluded.

**Result.** True, for every α > 0, as an immediate corollary of the 2026 proofs of
Gabrielov–Novikov–Shapiro's Conjecture 1.9 (X. Duan; G. Oliveira): a nonconstant Ψ of this form has
at most 2N − 1 critical points.

**Argument.** Let Ψ be nonconstant with N combined nonzero charges. By Oliveira's Theorem 1 (with
p = 2α), Ψ has at most 2N − 1 critical points, so all of them are isolated and every local maximum
is strict. If m_1 < m_2 are consecutive local maxima, the minimum of Ψ on [m_1, m_2] is not
attained at an endpoint (strictness), so it is an interior critical point other than m_1, m_2.
Hence M local maxima force at least 2M − 1 critical points, and 2M − 1 ≤ 2N − 1 gives M ≤ N.
The same count gives at most N − 1 local minima.

Remark (singular case). If some y_i = 0, Oliveira's bound still counts critical points in the
domain R \ {x_i : y_i = 0}, but a negative charge on the line separates the domain and the
argument above does not apply across such a pole; that case is not covered here.

Lean: —.

### [shapiro-12](shapiro-12/): Forsgård–Shapiro Conjecture 9 (c̃_k parity bound) is false

Lean: [witness](shapiro-11/shapiro_11.lean).

### [shapiro-13](shapiro-13/): Forsgård–Shapiro Conjecture 10 (c_k parity bound) is false

Lean: [witness](shapiro-11/shapiro_11.lean).

### [topp-67](topp-67/): fair partitions of convex polygons into n convex pieces

**Source.** The Open Problems Project, Problem 67 (Demaine, Mitchell, O'Rourke; https://topp.openproblem.net/p67), listed at https://amathr.org/problems/. Paraphrase: can every convex polygon be partitioned into n convex pieces that all have the same area and the same perimeter, for every n? (Nandakumar and Ramana Rao.)

**Result.** Yes, for every n ≥ 2. The TOPP page (read 2026-11-06) still lists the problem as open, with n = 2, 3, 4 and prime powers n = p^k settled (Nandakumar-Ramana Rao; Bárány-Blagojević-Szűcs; Aronov-Hubard and Karasev 2010). The secondary questions on the page (deciding feasibility for a given polygon, minimising total cut length, higher dimensions for non-prime-power n) are not addressed here.

**Argument.** Not reproduced (literature result). Akopyan, Avvakumov and Karasev prove that every convex body in the plane, in particular every convex polygon, has a partition into m convex parts of equal area and equal perimeter for every integer m ≥ 2. The prime-power case uses an equivariant-topology (configuration space / Voronoi) argument; they extend it to all m by an inductive cutting scheme with a degree computation.

Lean: —.

### [froberg-4.3](froberg-4.3/): two generic quadrics in the exterior algebra (even n proved elsewhere; odd n open)

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and from the
other pockets*, Arnold Math. J. 4 (2018), Section 4.4, Conjecture 4.3 (from V. Crispin Quiñonez,
S. Lundqvist, G. Nenashev, J. Pure Appl. Algebra 223 (2019), arXiv:1803.08918, "CLN"), listed via
https://amathr.org/problems/. Paraphrase: for generic quadratic forms f, g in the exterior algebra
E on n generators and generic linear forms ℓ_1, ℓ_2 in S = C[x_1..x_n],
HS(E/(f, g)) = HS(S/(x_1², …, x_n², ℓ_1², ℓ_2²)) = Σ_s a(n, s) t^s, where a(n, s) counts lattice
paths with steps (±1, +1) from the bottom-left to the top-right corner of an
(n + 2 − 2s) × (n + 2) rectangle.

**Result (status).** The statement about S/(x_i², ℓ_1², ℓ_2²) is proved for all n, and the
statement about E/(f, g) is proved for even n (M. Boij, S. Lundqvist 2026, with CLN Theorem 1).
For odd n the exterior-algebra statement remains open; CLN verified it by computer for odd
n ≤ 19, proved the upper bound dim(E/(f,g))_s ≤ a(n, s) for all n, and determined the first
⌊n/3⌋ + 1 and the last nonzero coefficient.

**Reduction for odd n (re-derived).** Let n be odd, A = E_{n+1}/(F, G) with F, G generic (even
case, so HS(A) = Σ a(n+1, s) t^s by Boij–Lundqvist), z a generic linear form, and h_s the
dimension of the homology ker(z)/im(z) of multiplication by z on A in degree s. Then
A/zA ≅ E_n/(f, g) with f, g generic, and the exact count
dim(A/zA)_s = a(n+1, s) − dim(A/zA)_{s−1} + h_{s−1}
shows: the conjecture for odd n holds iff h_{s−1} = a(n, s) + a(n, s−1) − a(n+1, s) for all s
(certificate/apaths.py tabulates both sides of the needed identity and checks the closed formula
for a(n, s) against direct path counts for n ≤ 23). Since h ≥ 0, this also gives
dim(E_n/(f,g))_s ≥ a(n+1, s) − a(n, s−1), which recovers the known coefficients only
(s ≤ ⌊n/3⌋ + 1). A mod-p check (certificate/zhom.py, run from the certificate directory) gives h = (0,0,1,1,0,0)
for n = 5 and h_3 = 6, h_4 = 1 for n = 7, as predicted. CLN Theorem 3 gives the explicit generic form for odd n = 2k + 1:
f = Σ_{i≤k} x_i x_{k+i}, g = Σ_{i≤k} x_i x_{k+1+i}.

Lean: —.

### [aimmatrix-sap3](aimmatrix-sap3/): fewest nonzeros of an irreducible β-arbitrary pattern (partial)

**Source.** I.-J. Kim, A. W. Wehe, *Open Questions*, AIM workshop "Spectra of families of
matrices described by graphs, digraphs and sign patterns" (October 2006; report dated
2007-09-03), Section 2, question Q3, listed via https://amathr.org/problems/. Write
det(xI − A) = x^n + α_1 x^{n−1} + … + α_n. A pattern is β-arbitrary (β ⊆ {1, …, n}) when every
choice of real values for the α_i, i ∈ β, is attained by some realization. Q3: for 1 ≤ k ≤ n, the
least number m(n, k) of nonzero entries of an n×n irreducible sign (or zero-nonzero) pattern that
is β-arbitrary for some β with |β| = k.

**Reading.** For k = n the only choice is β = {1, …, n}, so m(n, n) is the minimum for irreducible
spectrally arbitrary patterns: the 2n-conjecture says m(n, n) = 2n (known: ≥ 2n − 1). Q3 therefore
contains that conjecture. The values below hold for sign and for zero-nonzero patterns alike (the
lower bounds are proved for zero-nonzero patterns, the constructions are sign patterns).

**Result (partial).**
- m(n, 1) = n + 1 for n ≥ 3, and m(2, 1) = 4.
- m(n, 2) = n + 2 for n ≥ 4, and m(3, 2) = 6, m(2, 2) = 4.
- m(n, k) ≤ n + k whenever k ≥ 2 divides n; with the dimension bound, m(n, k) ∈ {n + k − 1, n + k}
  in that case.
- Table for n ≤ 6: m(3, ·) = 4, 6, 6; m(4, ·) = 5, 6, 7, 8; m(5, k) = 6, 7, 8, 9 for k = 1..4
  (m(5, 5) not decided here); m(6, k) = 7, 8, 9, 10 for k = 1..4.
  So m(n, k) = n + k in every computed case except (n, k) = (2, 1)
  and (3, 2). Data suggest: a strongly connected digraph with n vertices and cyclomatic number
  c ≤ n − 2 has at most c − 1 coefficients with two monomials (true for n ≤ 6), which would give
  m(n, k) ≥ n + k for k ≤ n − 2.

**Argument.** - Terms. α_i is a signed sum over collections of vertex-disjoint cycles of the digraph covering i
  vertices, each collection giving its own monomial in the entries (no cancellation). Two-term
  lemma: if α_i is β-prescribable then α_i has at least two monomials, because the target 0 must
  be attained and a monomial in nonzero entries never vanishes.
- Dimension. Diagonal similarity fixes n − 1 entries on a spanning tree, so m − n + 1 ≥ k
  (multiaffine map onto R^k), that is m ≥ n + k − 1.
- k = 1 lower bound: an irreducible pattern with n nonzeros is one n-cycle (one monomial in α_n,
  none elsewhere).
- k = 2 lower bound: an irreducible pattern with n + 1 nonzeros is a cycle plus one ear, so its
  digraph has exactly two cycles, and they share a vertex. Every α_i has at most two monomials and
  at most one α_i has two. So at most one coefficient can be prescribed.
- k = 1 construction (n + 1 entries): two cycles of equal length L sharing a vertex (n = 2L − 1)
  or two internally disjoint u→v paths of length L ≥ 2 plus a v→u path of length q ≥ 1
  (n = 2L + q − 1), with cycle weights of opposite signs: α_L = −(w_1 + w_2) takes every value.
- k = 2 construction (n + 2 entries, n ≥ 4): pick a with 2a ≤ n ≤ 4a − 2 and 1 ≤ j, l ≤ a with
  j + l = 4a − n; set r = n − 2a. Cycles C1 = u_1 → … → u_a → u_1, C2 = v_1 → … → v_a → v_1
  (disjoint) and C3 = u_1 → … → u_j → v_1 → … → v_l → z_1 → … → z_r → u_1 (length 2a). The
  digraph has n vertices, n + 2 arcs and exactly the cycles C1, C2, C3 (every cycle through the arc
  u_j → v_1 is C3). Hence α_a = −(w_1 + w_2), α_{2a} = w_1 w_2 − w_3. With signs w_1 > 0, w_2 < 0,
  w_3 < 0: given targets (s, t), choose w_1 + w_2 = −s with |w_1 w_2| > max(0, −t), then
  w_3 = w_1 w_2 − t < 0. So the sign pattern is {a, 2a}-arbitrary.
- Blow-up (k | n, n = tk). Take a k×k irreducible spectrally arbitrary sign pattern with 2k
  nonzeros (exists for every k ≥ 2, Britz et al. 2004). Replace each vertex v by a directed path
  v_1 → … → v_t (arcs of sign +), arcs u → v becoming u_t → v_1 and a loop at v becoming v_t → v_1.
  The result is irreducible with tk = n vertices and 2k + (t − 1)k = n + k arcs, and its cycles
  correspond to the old ones with all lengths multiplied by t, so a realization with path entries 1
  has characteristic polynomial p(x^t) where p is that of the original realization. Hence the new
  pattern is {t, 2t, …, kt}-arbitrary.
- n = 3, k = 2: the six irreducible 3×3 zero-nonzero patterns with 5 nonzeros each have at most
  one coefficient with two monomials (enumeration `certificate/enum.c`, symbolic
  coefficients in the work REPORT), so m(3, 2) ≥ 6; a 6-entry witness passes the test below.
- n ≤ 5 table. `certificate/enum.c` enumerates all irreducible n×n zero-nonzero patterns with m
  nonzeros up to permutation similarity and transposition and counts monomials of each α_i
  exactly (permanents of principal 0/1 submatrices). Lower bounds: for (3,2), (4,2), (4,3), (5,2),
  (5,3) no pattern with m(n, k) − 1 entries has k coefficients with two monomials. For (4,4) at
  m = 7 and (5,4) at m = 8 the only candidates (one and two patterns) satisfy α_3 = −a_{04}a_{40}·α_1
  (sympy, see REPORT), so α_1 = 0 forces α_3 = 0 and they are not {1,2,3,4}-arbitrary. Upper
  bounds: `certificate/tester.py` finds, by Newton's method, a realization with α_β = 0, all
  entries away from 0 and the Jacobian of α_β of rank k (nilpotent-Jacobian test: the implicit
  function theorem plus the scaling A ↦ tA, which multiplies α_i by t^i, give every target);
  logs `certificate/n34.out`, `certificate/n5.out`, `certificate/n6.out` (n = 6 with the 64-bit
  enumerator `certificate/enum64.c`: no pattern with m = 7, 8, 9 has 2, 3, 4 two-monomial
  coefficients; a 10-entry {1,2,3,4}-witness).

Lean: —.

### [froberg-H](froberg-H/): T_{n,2,2} = S/(x_1², …, x_n²)² has the WLP for every n

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and from the other
pockets*, Arnold Math. J. 4 (2018), §2.3, Problem H (paraphrased): when do T_{n,d,k} = S/(x_1^d, …, x_n^d)^k have
the WLP and the SLP? The text recalls that T_{n,2,2} has the WLP for odd n (Boij–Fröberg–Lundqvist, J. Algebra 495
(2018), Theorem 22) and that this is believed for even n; the BFL proof does not apply there.

**Reading.** S = C[x_1, …, x_n] (characteristic 0, any field of characteristic 0 or > 2 works for the new step),
WLP with respect to ℓ = x_1 + … + x_n (for monomial algebras the WLP holds iff it holds for this ℓ).

**Result.** Partial answer to Problem H (the example it names): T_{n,2,2} has the WLP for every n. New for
even n. The general classification of WLP/SLP for T_{n,d,k} stays open.

**Argument.** BFL's proof of Theorem 22 works verbatim for even n = 2k in every degree except the map
×ℓ: R_{k+1} → R_{k+2} (their closing remark). We prove that this map is injective
(dim R_{k+1} < dim R_{k+2}; dimension check below).

Basis of R_t: x_S (S ⊂ [n] squarefree, |S| = t), x_i² x_T (i ∉ T, |T| = t−2), x_i³ x_R (i ∉ R, |R| = t−3);
x_i²x_j² = x_i⁴ = 0. Write U (up) and D (down) for the Boolean-lattice maps U f(S) = Σ_{x∈S} f(S∖x).
Multiplying v = Σβ(S)x_S + Σγ(i,T)x_i²x_T + Σδ(i,R)x_i³x_R ∈ R_{k+1} by ℓ and reading coefficients:
(i) Uβ = 0 (squarefree part, level k+1 → k+2 on [2k]);
(ii) link_i β + Uγ_i = 0 for every i, where link_i β(T) = β(T ∪ i) on k-subsets of [2k]∖i;
(iii) γ_i + Uδ_i = 0.
So ℓv = 0 iff β ∈ ker U and link_i β = U²δ_i for all i; U² from level k−2 to k on 2k−1 points is injective, so
v = 0 iff β = 0. Thus injectivity ⇔ Φ: ker U → ⊕_i Fun_k([2k]∖i)/Im U², β ↦ (link_i β mod Im U²)_i, is injective.
By the sl₂ (Specht) decomposition of the Boolean lattice, ker U at level k+1 on [2k] is the irreducible
S_{2k}-module S^{(k+1,k−1)}, spanned by β = U²v with v = Π_{r<k}(e_{a_r} − e_{b_r}) (k−1 disjoint pairs, two
further points c, d). Φ is S_{2k}-equivariant, so by Schur it is injective or zero. It is not zero:
Im U² = (ker D²)^⊥, and w = Uv' with v' = Π_r(e_{a_r} − e_{b_r}) on [2k]∖c satisfies Dv' = 0 and DU − UD = 1 at
level k−1 on 2k−1 points, so D²w = Dv' = 0; and ⟨link_c β, w⟩ = Σ_T β(T∪{c,d})·w(T∪{d}) = Σ_T 2·sign(T)² = 2^k,
the sum over the 2^{k−1} transversals T of the pairs (sets T ∪ {y} with y a partner of an element of T give
w = 0 by cancellation). Hence Φ ≠ 0, Φ is injective, and ×ℓ: R_{k+1} → R_{k+2} is injective.

Dimension check: dim R_t = C(2k,t) + 2k·C(2k,t−2) (the x_i²-, x_i³-monomials form n copies of the Boolean level
t−2 on n points, as in BFL), and dim R_{k+2} − dim R_{k+1} = C(2k,k)/(k+1)·(2k − 3k/(k+2)) > 0.

Lean: needs Mathlib.

### [froberg-O](froberg-O/): periods of the zero-set map φ on F_p[x]: period 6 occurs (partial)

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and from the
other pockets*, Arnold Math. J. 4 (2018), Section 4.3, Problem O, listed via
https://amathr.org/problems/. Paraphrase: φ(f) = Σ_{a ∈ Z(f)} x^a, where Z(f) ⊆ F_p is the zero set
and a is read as an integer in {0, …, p − 1}. For n = 1, which period lengths occur? The paper: the
4-cycle 0 → 1 + x + … + x^{p−1} → x → 1 → 0 for every p; by exhaustive search no other period for
p ≤ 17; a 2-cycle at p = 71; periods are always even (stated as easy).

**Reading.** After one step every state is a 0/1 polynomial, i.e. a set S ⊆ {0, …, p − 1} of
exponents, and φ acts by S ↦ {b ∈ F_p : Σ_{a∈S} b^a = 0} (0^0 = 1).

**Result (partial).**
- Evenness (re-proved, in Lean): 0 ∈ φ(S) iff 0 ∉ S, so membership of 0 alternates along every orbit
  and every period is even.
- Exhaustive census for p ≤ 31: the only cycle is the standard 4-cycle (p = 19, 23, 29, 31 are new;
  p = 29 has 114356 image sets, p = 31 has 199235).
- Period 6 occurs: at p = 1009,
  {472, 553, 786, 868} → {0, 121, 144} → {446, 495} → {0, 74, 150, 578, 615, 707, 904, 1008}
  → {103, 322, 775} → {0, 337, 506, 561, 759, 922, 951} → {472, 553, 786, 868}
  (six distinct states; Lean `cycle1009`, `period_six_1009`). So the known lengths are 2, 4, 6.
- Small-support search: every cycle reached from a set of size ≤ 2 for all primes p ≤ 593, of size
  ≤ 3 for p ≤ 139, of size ≤ 4 for p ≤ 59: periods 2 and 4 only. Random search (200 random starts
  of size 1 to 3 for each of the 382 primes 1000 < p < 4000): 32 cycles of period 2, 2 of period 4
  (p = 1877, 2311, besides the standard one), 1 of period 6 (p = 1009). The small-support
  search found 2-cycles at p = 71, 127, 151 (two), 181, 367, 373, 397, 409, 421 (two), 431, 449; a second, non-standard
  4-cycle at p = 541: {129, 411} → {0, 52, 216, 268, 273, 325, 489} → {120, 133, 529} → {0, 163, 362}
  → {129, 411}.
- Structure: for b = g^j ≠ 0 (g a primitive root), Σ_{a∈S} b^a is the discrete Fourier transform over
  F_p of the indicator of S reduced mod p − 1 (exponents 0 and p − 1 coincide), so φ is "zeros of a
  DFT" followed by j ↦ g^j read as an integer. This mixes the additive and multiplicative structure
  of F_p, which is why the cycles look sporadic.

Lean: [witness](froberg-O/froberg_O.lean).

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

### [froberg-R](froberg-R/): explicit odd-degree forms with the Lundqvist–Nicklasson series (partial)

**Source.** R. Fröberg, S. Lundqvist, A. Oneto, B. Shapiro, *Algebraic stories from one and from the
other pockets*, Arnold Math. J. 4 (2018), Section 4.4, Problem R, listed via
https://amathr.org/problems/. Paraphrase: for each n and odd d, find an explicit form f of degree d
in the exterior algebra E on n generators such that E/(f) has the minimal series given by
Lundqvist–Nicklasson (S. Lundqvist, L. Nicklasson, *On generic principal ideals in the exterior
algebra*, arXiv:1803.03563, "LN", Corollary 3.2: a lower bound a = b + c, in lexicographic order,
for HS(E/(f)) for every odd form f).

**Reading.** "Minimal series" = the LN bound a. It is not attained at (n, d) = (9, 3) (LN Prop. 4.4),
which is excluded. LN already give explicit forms for d = n − 2 and for d = n − 3, n even, and say
that they found none for d = n − 4.

**Result (partial).**
1. Certification principle. For an integer form f, rank over Q ≥ rank mod p gives HS_Q(f) ≤ HS_p(f)
   coefficientwise, while HS_Q(f) ⪰_lex a by LN Cor. 3.2. So HS_p(f) = a for one prime p implies
   HS_Q(f) = a, and then a is also the generic (minimal) series for that (n, d).
2. d = n − 4, n odd (new reduction). HS(E/(f)) = a iff the symmetric bilinear form
   B_f(α, β) = [α ∧ β ∧ f] on E_2 is nondegenerate. (Degrees below n − 4 are free; degree n − 4 needs
   f ≠ 0; degrees n − 2, n − 3, n − 1, n need rank B_f = C(n,2), injectivity of ·f on E_1,
   surjectivity of ·f: E_3 → E_{n−1} and f ≠ 0; nondegeneracy of B_f implies injectivity on E_1, since
   x·f = 0 gives B_f(x∧y, ·) = 0, and LN Prop. 2.2 turns injectivity on E_1 into surjectivity on E_3.
   The LN bound in these degrees is C(n,4) − 1, C(n,3) − n, 0, 0, 0, checked against the formula.)
3. Explicit family for d = n − 4: f_n = Σ_{|S|=4} (max S − min S)·sgn(S, S^c)·e_{S^c} (the Hodge dual
   of η = Σ_S (max S − min S) e_S). Then B_f[P, Q] = ±(max(P∪Q) − min(P∪Q)) for disjoint pairs P, Q
   (sign: − for crossing pairs). This matrix has full rank mod 1000003 for every odd n, 7 ≤ n ≤ 23,
   so E/(f_n) has the LN series for d = n − 4, n = 7, 9, …, 23 (n = 7 is d = 3). A proof of
   nondegeneracy for all odd n is open (the determinants have no visible pattern:
   432, −219948493824, … for n = 7, 9).
4. Sparse cyclic forms for all small cases: for every odd d with 3 ≤ d ≤ n − 2 and 5 ≤ n ≤ 13,
   (n, d) ≠ (9, 3), the orbit sum of one or two "seed" d-subsets under the rotation i ↦ i + 1 mod n
   (coefficients 0, ±1) attains a; table in certificate/seeds_table.out (e.g. d = 3:
   Σ_i x_i x_{i+1} x_{i+2} for n ≤ 10, Σ_i x_i x_{i+1} x_{i+3} for 6 ≤ n ≤ 14, n ≠ 9; the latter fails at
   n = 15).
5. Consequence for LN Question 6.1 (is a the minimal series for (n, d) ≠ (9, 3)?): yes in the new cases
   (n, d) = (12, 7), (13, 7), (13, 9), (15, 11), (17, 13), (19, 15), (21, 17), (23, 19), beyond LN
   Prop. 4.5 (d = 3, n ≤ 17; d = 5, n ≤ 13; d = 7, n ≤ 11) and LN Props. 4.1–4.2 (d = n − 2, n − 3).

Lean: —.

