# Cooper problem 38: the Linial-Luria count of d-dimensional permutations is tight (Keevash)

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

**Evidence.** Keevash arXiv:1802.05900v1, Section 1 (Theorem 1.8 and the paragraph before it),
read 2026-11-06. No Lean (asymptotic enumeration via the existence-of-designs machinery).
Outside Lean: everything.

**Review level.** `agent` (statement located and matched; proof not re-derived).

**Prior art.** Keevash 2018 (above). Searched: web (Linial-Luria lower bound), arXiv abstract
and full text of 1802.05900, google-deepmind/formal-conjectures HEAD 2026-11-06 (no entry).
