# GEO C1.3: repeated subdivision of tetrahedra with a(T)/r(T) bounded (Hajós)

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991), C1 (end of section), citing G. Hajós, Problem 122, Colloq. Math. 3 (1954) 74. Paraphrase: with a(T) the longest edge and r(T) the inradius of a tetrahedron T, give an effective way to decompose any T into finitely many tetrahedra, then each of those, and so on, so that a/r stays bounded over all generations.

**Reading.** The pieces are meant to shrink (otherwise "do not subdivide" works); the construction below halves the diameter at every generation.

**Result.** Yes; answered by Freudenthal in 1942 (for simplices of every dimension, as an answer to a question of Brouwer).

**Argument.** Write T = A(S) with A affine and S = {1 ≥ x1 ≥ x2 ≥ x3 ≥ 0} (Kuhn simplex). Generation k cuts S by the hyperplanes x_i = m/2^k and x_i − x_j = m/2^k (m integer). All facet hyperplanes of S belong to this arrangement, and inside each cube of side 2^−k the arrangement gives the 3! = 6 Kuhn simplices S_π (π a permutation) scaled by 2^−k. So S is a union of 2^(3k) translates of the S_π/2^k, generation k+1 refines generation k, and the pieces of T are translates of A(S_π)/2^k. a/r is invariant under translation and scaling, so over all generations it takes at most 6 values (Freudenthal; Bey shows 3 congruence classes suffice for tetrahedra with a suitable vertex order). The construction is explicit.

**Evidence.** Citation plus the re-derivation above; no Lean (Euclidean geometry of polytopes). Outside Lean: the whole argument.

**Review level.** `rechecked` (argument re-derived).

**Prior art.** Verdict `known`.
- H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. (2) 43 (1942) 580-582, doi:10.2307/1968813 (answers Brouwer's question on infinite sequences of subdivisions of bounded flatness).
- J. Bey, *Tetrahedral grid refinement*, Computing 55 (1995) 355-378; J. Bey, *Simplicial grid refinement: on Freudenthal's algorithm and the optimal number of congruence classes*, Numer. Math. 85 (2000) 1-29.
Freudenthal predates Hajós's 1954 problem; CFG do not mention it. Searched: web, google-deepmind/formal-conjectures (local clone 2026-11-06) (2026-11-06).
