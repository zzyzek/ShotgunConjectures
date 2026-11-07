# AMR shapiro-3: a line restriction of N point-charge potentials has at most N local maxima

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

**Evidence.** No Lean file. Outside Lean: the cited critical-point theorem and the elementary
count above.

**Review level.** `rechecked` (the corollary step re-derived; the cited theorem not re-proved).

**Prior art.** X. Duan, *Critical points of line restrictions of signed point-charge potentials*,
arXiv:2608.28376 (2026); G. Oliveira, *Critical points of point charge potentials along lines*,
arXiv:2609.00336 (31 Aug 2026), Theorem 1: for every p > 0, a nonconstant restriction to a line of
Σ ζ_j |X − A_j|^{−p} has at most 2N − 1 distinct critical points (Conjecture 1.9 of A. Gabrielov,
D. Novikov, B. Shapiro, *Mystery of point charges*, Proc. LMS 95 (2007) 443–472). Neither paper
states the local-maxima corollary explicitly (Oliveira's abstract and text checked). Searched
2026-11-07: web search; google-deepmind/formal-conjectures (no entry).
