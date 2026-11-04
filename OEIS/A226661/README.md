# OEIS A226661: 3x+k cycles with exactly n odd elements exist for every n

**Source.** OEIS [A226661](https://oeis.org/A226661): Smallest positive integer k (or 0 if no such k) with a primitive cycle of positive integers, exactly n of which are odd, under iteration by the Collatz-like 3x+k function. Conjecture: "a(n)>0 for all n." (OEIS text, CC BY-SA 4.0.) A cycle is primitive
if its elements are not a common multiple of the elements of another cycle, i.e. the gcd of its
elements is 1.

**Result.** True: an explicit primitive cycle exists for every admissible size, so a(n) > 0
(this gives an upper bound for a(n), not its value).

**Argument.** T_k(x) = x/2 (x even), (3x+k)/2 (x odd). Take m ≥ 1 with 2^(n+m) > 3^n and gcd(3^n - 2^n, 2^m - 1) = 1, and k = 2^(n+m) - 3^n (odd, prime to 3). With y_j = 3^j 2^(n-j) (2^m - 1) and x_j = y_j - k (0 ≤ j ≤ n): x_0 = 3^n - 2^n > 0; for j < n, x_j is odd and T_k(x_j) = (3y_j - 2k)/2 = y_(j+1) - k = x_(j+1); x_n = 2^m (3^n - 2^n), and m halvings return to x_0. The n odd elements increase strictly and the m even ones are 2^i (3^n - 2^n), 1 ≤ i ≤ m, so this is a cycle with exactly n odd elements. Primitive: the gcd of the elements divides x_0 and 2x_1 - 3x_0 = k, and gcd(x_0, k) = gcd(3^n - 2^n, 2^n(2^m - 1)) = gcd(3^n - 2^n, 2^m - 1) = 1. A suitable m exists: any prime m > 3^n/2, since a prime factor q of 2^m - 1 has ord_q(2) = m, so q ≡ 1 (mod m) and q > 3^n > 3^n - 2^n.

**Evidence.**
- Lean (Mathlib): [`A226661_mathlib.lean`](A226661_mathlib.lean) proves the full result (`A226661_main`): for every n >= 1 there are an odd k > 0 with 3 not dividing k and a cycle of T_k of positive, pairwise distinct integers with exactly n odd elements and gcd 1 (m a prime > 3^n; primitivity via ord_q(2) = m, Mathlib `orderOf_eq_prime`, `ZMod.orderOf_dvd_card_sub_one`), so a(n) > 0. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A226661.lean`](A226661.lean) (core Lean): for all n ≥ 1 and all m with 3^n < 2^(n+m): k odd, `step` (x_j odd and T_k x_j = x_(j+1)), `top` (x_n = 2^m (3^n - 2^n)), `halve`, `x0_eq`; and `choice_small`: explicit m for 1 ≤ n ≤ 30. Outside Lean: k prime to 3, existence of m for n > 30 (prime m argument: needs infinitely many primes and Fermat's little theorem), the Euclid steps for gcd(x_0, k), and distinctness of the elements.
- `certificate/collatz_k_cycles.py` (scan): simulates the three constructions (A226661, A226676,
  A226677) and checks odd count, length, positivity and gcd 1 for n ≤ 40.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A226661_mathlib.lean`](A226661_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A226661.lean`](A226661.lean) checks the parts named under Evidence.

**Prior art.** Partly known. [OEIS A226661](https://oeis.org/A226661) (fetched 2026-11-04) still states the conjecture. It follows at once from [Lagarias, Acta Arith. 56 (1990)](http://matwbn.icm.edu.pl/ksiazki/aa/aa56/aa5614.pdf), Theorem 2.1 (each parity vector gives a rational cycle, denominator 2^L - 3^n) and the correspondence with primitive cycles of T_k in Section 1, by choosing an irreducible parity vector of the right length and number of ones; this corollary is not written there or in OEIS. Searched: entry, OEIS cross-reference search, edit history, Lagarias 1990, web. Worth an OEIS comment citing Lagarias. (Prior-art review 2026-11-04.)
