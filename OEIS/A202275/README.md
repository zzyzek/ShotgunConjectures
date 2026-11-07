# OEIS A202275: a(n) < 0 for 687 <= n <= 10^8, and a(n) -> -infinity

**Source.** [A202275](https://oeis.org/A202275), differences between A074753 (number of k with sigma(k) <= n) and
A202276 (number of k <= n with sigma(x) = k unsolvable). Conjectures (J. Krizek): "Max a(n) = 15 for n = 195, 403,
434. For n >= 687, a(n) < 0." (entry checked 2026-11-07).

**Reading.** The listed data equal C(n) - (n - V(n)) with C(n) = #{k : sigma(k) <= n} and
V(n) = #{v <= n : v = sigma(k) for some k}. (A074753 is now defined with sigma(k) < n, which shifts the index by
one; the data of A202275 follow the "<= n" form: a(1) = 1, a(2) = 0, a(3) = 1, ...)

**Result (partial).**
1. For 687 <= n <= 10^8, a(n) < 0; the maximum of a(n) over n <= 10^8 is 15, attained exactly at n = 195, 403,
   434; a(686) = 0 is the last nonnegative value (computation).
2. a(n) = (c - 1 + o(1)) n with c = 0.6727... (A308039), so a(n) < 0 for all n beyond some N0. This follows
   from two known theorems: C(n) ~ c n (Erdős; elementary proof Dressler 1972, cited in A074753) and
   V(n) = o(n) (the values of sigma have density 0; Erdős; order of magnitude by K. Ford, 1998; these two citations are from memory and were not re-read).
   Both conjectures follow if N0 <= 10^8, which the cited proofs do not give.

**Why the gap is not closed.** An explicit V(n) bound of the elementary kind (values not divisible by 2^j come
from k with fewer than j odd primes to an odd power) gives V(n) <= n/2^j + #{k : sigma(k) <= n, fewer than j such
primes}; the second term is about n (log log n)^(j-2) / log n and beats the available slack
(1 - c - V(n)/n ≈ 0.17 at 10^8) only for n far beyond 10^8 (around e^35 for j = 3).

**Evidence.**
- [`certificate/a202275.c`](certificate/a202275.c): divisor-sum sieve; prints the first 84 terms (equal to the
  entry's data), checkpoints, the maximum and the last nonnegative n.
  [`certificate/run1e8.out`](certificate/run1e8.out): run with N = 10^8 (a(10^8) = -16940337,
  C/n = 0.67275, V/n = 0.15785).
- Lean: none. Outside Lean: the computation for n <= 10^8 and the two cited asymptotic theorems.

**Review level.** `rechecked` (computation; asymptotic part from the literature).

**Prior art.** OEIS A202275, A074753 (Dressler 1972), A202276, A308039; google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs: no file (2026-11-07). The b-file reaches n = 10^4.
