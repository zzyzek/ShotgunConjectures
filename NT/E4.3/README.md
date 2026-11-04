# Guy E4: Erdős's last question on primitive sets — the x²/6 guess is too small

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section E4 (p. 314). From an email Erdős sent a month before he died: for a
primitive set A ⊆ [1, x] (no element divides another), with f(A; n) the number of a_i < n, how
large can Σ_(n≤x) f(A; n) be? Is the maximum x²/6 + O(x), attained perhaps by the integers in
(x/3, 2x/3]?

**Reading.** The email is partly garbled in our copy. We read the sum as Σ_(n≤x) f(A; n) =
Σ_(a∈A) (x − a) (each a is counted for n = a + 1, …, x). This reading is supported by the
book's own numbers: the set (x/3, 2x/3] gives (x/3)(x/2) = x²/6. Counting a_i ≤ n instead
changes the sum by |A| ≤ x, inside the O(x).

**Result.** Under this reading the answer is no: the maximum is at least (13/64)x² − O(x)
≈ 0.2031x² > x²/6.

**Argument.** A = (x/4, x/2] ∪ {odd a ∈ (x/2, 3x/4]} is primitive: two elements of (x/4, x/2]
have ratio < 2; an odd a ∈ (x/2, 3x/4] and b ∈ (x/4, x/2] have 1 < a/b < 3, so b | a would
force a = 2b, which is even; two odd elements of (x/2, 3x/4] have ratio < 2. Its sum is
(x/4)(5x/8) + (x/8)(3x/8) + O(x) = (10/64 + 3/64)x² + O(x).

**Evidence.** `certificate/e43_check.py` (second reader): primitivity and the sum for
x = 12, 100, 1000, 1500, 10000 (S/x² = 0.2031 for large x), with a direct evaluation of
Σ f(A; n) for x ≤ 1500. The scan's max-flow optimum (≈ 0.2258x² at x = 1500,
`primwt.py`) was not rechecked. No Lean (an asymptotic statement; a single-x witness would not
refute an O(x) claim).

**Review level.** `rechecked`. The result depends on the reading of the garbled email.
**Prior art.** Nothing found on this question (searched: web, standard and extended, for the email and the x²/6 guess; erdosproblems.com primitive-set problems). Verdict: new, but the result depends on our reading of the garbled email. 2026-11-04.
