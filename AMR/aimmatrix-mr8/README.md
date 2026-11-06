# AMR aimmatrix-mr8: minimum rank of strict powers of a tree is not strictly decreasing

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

**Evidence.**
- Lean + Mathlib: [`aimmatrix_mr8_mathlib.lean`](aimmatrix_mr8_mathlib.lean). Main theorem
  `AimMr8.aimmatrix_mr8`: T is not a star, mr(T) = 5, mr(T^2) = 4, mr(T^3) = 4, hence
  ¬(mr(T^3) < mr(T^2)) and 2 < mr(T^2). The strict power is defined from the source's
  definition (walks of length exactly r, `walk`, `spow`), mr as the infimum of ranks over real
  symmetric matrices with the pattern. Axioms: propext, Classical.choice, Quot.sound.
  Checked with tools/leancheck-mathlib.sh, no warnings.
- `certificate/scan.py` (trees up to 11 vertices; lower bound n − Z(G) from the zero forcing
  number, upper bound the clique cover number), output `certificate/scan11.out`;
  `certificate/gen.py` (edge tables, triangular submatrices, the rank-5 matrix for T),
  `certificate/fact.py` (rank factorisation of that matrix), `certificate/um2.py`.
- Outside Lean: the scan (only used to find the example); the claim mr(T^4) = 2.

**Review level.** `lean-proof` for the counterexample.

**Prior art.** Searched 2026-11-06: L. DeAlba, J. Grout, I.-J. Kim, S. Kirkland, J. McDonald,
A. Yielding, *Minimum rank of powers of trees*, Electron. J. Linear Algebra 23 (2012) 151–163
(proves mr(T^(2)) ≤ mr(T) − 1 and mr(P_n^(r)) = n − r for r ≤ n − 3, so paths satisfy Q8; its last
section leaves the monotonicity of mr(T^(k)) for non-star trees open); G. J. Chang, J. C.-H. Lin,
*Minimum rank of powers of cycles and trees* (ordinary powers, not strict); web search;
google-deepmind/formal-conjectures (HEAD 2026-11-05, no entry). No answer to Q8 found.
