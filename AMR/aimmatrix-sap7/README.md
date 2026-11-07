# AMR aimmatrix-sap7: potentially nilpotent full sign patterns are spectrally arbitrary

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

**Evidence.** No Lean file (the argument uses the implicit function theorem and the Jordan form of
real nilpotent matrices). Outside Lean: the whole argument, which is a citation of Pereira's
theorem plus the short re-derivation above.

**Review level.** `rechecked` (re-derived as above; matches the published theorem).

**Prior art.** R. Pereira, *Nilpotent matrices and spectrally arbitrary sign patterns*, Electron.
J. Linear Algebra 16 (2007) 232–236 (the theorem, answering Q7 in the same year as the report).
Restated as Theorem 1.2 in I.-J. Kim, D. D. Olesky, B. L. Shader, P. van den Driessche, H. van der
Holst, K. N. Vander Meulen, *Generating potentially nilpotent full sign patterns*, Electron. J.
Linear Algebra 18 (2009) 162–175, which also lists an order-3 full pattern that satisfies (N1),
(N2) and is not spectrally arbitrary (so the nilpotence hypothesis cannot be dropped).
Searched 2026-11-07 (web search; google-deepmind/formal-conjectures has no entry for this
question).
