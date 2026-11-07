# AMR aimmatrix-sap3: fewest nonzeros of an irreducible β-arbitrary pattern (partial)

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

**Argument.**
- Terms. α_i is a signed sum over collections of vertex-disjoint cycles of the digraph covering i
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

**Evidence.** No Lean file. Outside Lean: everything. The k = 1, 2 statements are hand proofs;
the n ≤ 5 table rests on the exact C enumeration (lower bounds) and on floating-point
nilpotent-Jacobian witnesses (residual < 1e-9, smallest singular value bounded away from 0), which
are numerical certificates, not exact ones.

**Review level.** `agent`.

**Prior art.** Searched 2026-11-07: web search for β-arbitrary / partially prescribed
characteristic polynomial patterns; T. Britz, J. J. McDonald, D. D. Olesky, P. van den Driessche,
*Minimal spectrally arbitrary sign patterns*, SIAM J. Matrix Anal. Appl. 26 (2004) (2n − 1 bound,
the dimension argument); google-deepmind/formal-conjectures (no entry). No work on Q3 found.
