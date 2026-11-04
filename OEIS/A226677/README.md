# OEIS A226677: 3x-k cycles with exactly n odd elements exist for every n

**Source.** OEIS [A226677](https://oeis.org/A226677): Smallest positive integer k (or 0 if no such k) with a primitive cycle of positive integers, exactly n of which are odd, under iteration by the Collatz-like 3x-k function. Conjecture: "a(n)>0 for all n." (OEIS text, CC BY-SA 4.0.) A cycle is primitive
if its elements are not a common multiple of the elements of another cycle, i.e. the gcd of its
elements is 1.

**Result.** True: an explicit primitive cycle exists for every admissible size, so a(n) > 0
(this gives an upper bound for a(n), not its value).

**Argument.** T_k(x) = x/2 (x even), (3x-k)/2 (x odd). n = 1: the cycle {1} of T_1. For n ≥ 2 put k = 3^n - 2^(n+1) (positive, odd, prime to 3) and x_j = k + 3^j 2^(n-j), 0 ≤ j ≤ n. For j < n, x_j is odd and T_k(x_j) = x_(j+1); x_n = 2(3^n - 2^n) is even and T_k(x_n) = x_0 = 3^n - 2^n. The odd x_j (j < n) increase strictly, so this is a cycle of n + 1 elements with exactly n odd ones. Primitive: the gcd of the elements divides x_0 and 2x_1 - 3x_0 = -k, and gcd(3^n - 2^n, 3^n - 2^(n+1)) = gcd(3^n - 2^n, 2^n) = 1 since 3^n - 2^n is odd.

**Evidence.**
- [`A226677.lean`](A226677.lean) (core Lean): for all n ≥ 2: k > 0, k odd, 3 ∤ k, `step`, `close`, `x0_eq`; gcd(x_0, k) = 1 for 2 ≤ n ≤ 40 by `decide`. Outside Lean: gcd(x_0, k) = 1 for n > 40 (one line above) and the strict increase of x_j.
- `certificate/collatz_k_cycles.py` (scan): simulates the three constructions (A226661, A226676,
  A226677) and checks odd count, length, positivity and gcd 1 for n ≤ 40.
- Lean (Mathlib): [`A226677_mathlib.lean`](A226677_mathlib.lean), `A226677_main`: for every n ≥ 1 there are k > 0 and x₀ > 0 whose T_k-orbit is a cycle (minimal period N) of positive integers with gcd 1 and exactly n odd elements. Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Partly known. [OEIS A226677](https://oeis.org/A226677) (fetched 2026-11-04) still states the conjecture. It follows at once from [Lagarias, Acta Arith. 56 (1990)](http://matwbn.icm.edu.pl/ksiazki/aa/aa56/aa5614.pdf), Theorem 2.1 (each parity vector gives a rational cycle, denominator 2^L - 3^n) and the correspondence with primitive cycles of T_k in Section 1, by choosing an irreducible parity vector of the right length and number of ones; this corollary is not written there or in OEIS. Searched: entry, OEIS cross-reference search, edit history, Lagarias 1990, web. Worth an OEIS comment citing Lagarias. (Prior-art review 2026-11-04.)
