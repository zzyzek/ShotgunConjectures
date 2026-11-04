# Guy B40: totatives of large n contain k-term arithmetic progressions

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B40. Recamán asks whether, for each k, the totatives of every
sufficiently large n contain an arithmetic progression of length k.

**Result.** Yes, for every fixed k (elementary; very likely known).

**Argument.** Let D be the product of the primes ≤ k dividing n (D ≤ k!). Consider x_j(t) =
1 + jDt for 0 ≤ j < k and 1 ≤ t ≤ T = ⌊(n − 2)/((k − 1)D)⌋, so all terms lie in [1, n − 1].
For a prime p ≤ k dividing n, x_j ≡ 1 (mod p). For a prime p > k dividing n, D is invertible
mod p and x_j ≡ 0 (mod p) for some 1 ≤ j < k excludes at most k − 1 classes of t mod p.
Inclusion–exclusion over the set S of primes p > k dividing n gives at least
T·∏_(p∈S)(1 − (k − 1)/p) − k^|S| admissible t. Each factor is ≥ 2/(k + 1), and |S| ≤ ω(n) =
O(log n / log log n), so the main term is n^(1−o(1)) while k^|S| = n^(o(1)). For n large
(depending on k) some t is admissible, and x_0(t), …, x_(k−1)(t) is a k-term progression of
totatives.

**Evidence.** Hand proof. [`B40_3_mathlib.lean`](B40_3_mathlib.lean) (Mathlib): `B40_3_main`
proves the result with explicit N = 2^(4·2^(8k)+8): a and d > 0 with 1 ≤ a + jd < n and
gcd(a + jd, n) = 1 for all j < k. The Lean proof replaces the inclusion–exclusion sieve by a union
bound: with L = log₂ n, B = ⌊L/4⌋, d = B# (primorial) and terms 1 + d(u + j), u < B, each prime
p > B dividing n spoils at most k values of u (since p > B), and the number m of such primes
satisfies k·m < B because (B+1)^m ≤ n and log₂ B ≥ 8k. Outside Lean: nothing.

**Review level.** `lean-proof` ([`B40_3_mathlib.lean`](B40_3_mathlib.lean)). Before:
`rechecked` (argument re-derived by the second reader; the scan's note used the same sieve with
difference D).
**Prior art.** Known: [P. Stumpf, arXiv 1408.0909 (2014)](https://arxiv.org/abs/1408.0909) answers Recamán's question exactly (the longest AP among the totatives of n tends to infinity), by elementary means. 2026-11-04.
