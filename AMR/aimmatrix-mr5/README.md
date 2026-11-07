# AMR aimmatrix-mr5: the minimum rank of the complement of the Kneser graph is n − 2k + 2

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

**Evidence.** [`certificate/check_construction.py`](certificate/check_construction.py): exact
rational check that the matrix above has exactly the required zero pattern and rank n − 2k + 2 for
(n, k) = (5,2), (6,2), (7,3), (8,3), (9,3), (9,4), (10,4) with integer nodes. For (8, 4) (n = 2k)
this particular divided-difference form vanishes on some intersecting pairs for every node choice
tried; n = 2k is the case the report already settles (rank 2), and Hu–Tang choose their
parameters differently. No Lean file. Outside Lean: the whole argument (citation of Hu–Tang; the
script re-checks the upper-bound construction in the listed cases only).

**Review level.** `rechecked` for the listed cases of the upper bound; otherwise citation.

**Prior art.** T. Hu, Q. Tang, *Minimum-rank parameters of complements of threshold Kneser graphs*,
arXiv:2607.06480 (v1 7 July 2026 titled "Minimum rank of complements of Kneser graphs"; v2
23 July 2026): mr = n − 2k + 2 over every infinite field and the real positive semidefinite minimum
rank equals it, for k ≥ 2, n ≥ 2k − 1; they state that this answers the AIM question. Open
strengthening: finite fields are not covered there. Searched 2026-11-07 (web search;
google-deepmind/formal-conjectures has no entry).
