# OEIS A226676: 3x-k cycles of every length N ≥ 3 exist

**Source.** OEIS [A226676](https://oeis.org/A226676): Smallest positive integer k (or 0 if no such k) with a primitive cycle of n positive integers under iteration by the Collatz-like 3x-k function. Conjecture: "For n>2, a(n)>0." (OEIS text, CC BY-SA 4.0.) A cycle is primitive
if its elements are not a common multiple of the elements of another cycle, i.e. the gcd of its
elements is 1.

**Result.** True: an explicit primitive cycle exists for every admissible size, so a(n) > 0
(this gives an upper bound for a(n), not its value).

**Argument.** T_k(x) = x/2 (x even), (3x-k)/2 (x odd). For N ≥ 3 put n = N - 1 ≥ 2, k = 3^n - 2^(n+1) = 3^(N-1) - 2^N (positive, odd, prime to 3) and x_j = k + 3^j 2^(n-j), 0 ≤ j ≤ n. For j < n, x_j is odd and T_k(x_j) = (3x_j - k)/2 = k + 3^(j+1) 2^(n-j-1) = x_(j+1); x_n = k + 3^n = 2(3^n - 2^n) is even and T_k(x_n) = 3^n - 2^n = x_0. The odd x_j increase strictly, so the cycle has exactly n + 1 = N elements. Primitive: the gcd of the elements divides x_0 and k, and gcd(3^n - 2^n, 3^n - 2^(n+1)) = gcd(3^n - 2^n, 2^n) = 1 because 3^n - 2^n is odd. (Same construction as OEIS-A226677.)

**Evidence.**
- [`A226676.lean`](A226676.lean) (core Lean): for all n ≥ 2: k > 0, k odd, 3 ∤ k, `step`, `close`, `x0_eq`; gcd(x_0, k) = 1 for 2 ≤ n ≤ 40 by `decide`. Outside Lean: gcd(x_0, k) = 1 for n > 40 (one line above) and the strict increase of x_j.
- `certificate/collatz_k_cycles.py` (scan): simulates the three constructions (A226661, A226676,
  A226677) and checks odd count, length, positivity and gcd 1 for N ≤ 42.
- Lean (Mathlib): [`A226676_mathlib.lean`](A226676_mathlib.lean), `A226676_main`: for every N ≥ 3 there are k > 0 and x₀ > 0 with `Function.minimalPeriod` (T_k) x₀ = N, all N orbit elements positive, and their gcd 1. The gcd for all n and the strict increase are proved there; nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Partly known. [OEIS A226676](https://oeis.org/A226676) (fetched 2026-11-04) still states the conjecture. It follows at once from [Lagarias, Acta Arith. 56 (1990)](http://matwbn.icm.edu.pl/ksiazki/aa/aa56/aa5614.pdf), Theorem 2.1 (each parity vector gives a rational cycle, denominator 2^L - 3^n) and the correspondence with primitive cycles of T_k in Section 1, by choosing an irreducible parity vector of the right length and number of ones; this corollary is not written there or in OEIS. Searched: entry, OEIS cross-reference search, edit history, Lagarias 1990, web. Worth an OEIS comment citing Lagarias. (Prior-art review 2026-11-04.)
