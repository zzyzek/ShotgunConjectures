# OEIS A036845 / A066437: phi/sigma tug-of-war — partial results

**Source.** [A036845](https://oeis.org/A036845) (J. L. Pe, 2002): a(n) = min_k T(n,k), where T(n,1) = phi(n),
T(n,2) = sigma(phi(n)), and phi and sigma alternate. Comments: "Conjecture: The sequence {T(n,k)} is eventually
periodic for every n, so a(n) can be computed in finite time." and "Conjecture: a(n) -> infinity as
n -> infinity." [A066437](https://oeis.org/A066437) (same author): a(n) = max_k T(n,k); "Conjecture: a(n) is
always finite; i.e. the sequence {T(n,k)} is eventually periodic for every n." Both b-files stop at n = 16384.
OEIS text, CC BY-SA 4.0, checked 2026-11-07.

**Result (partial).**
1. *Eventual periodicity (A036845 first conjecture = A066437).* Every seed n <= 2·10^8 is eventually periodic.
   The largest value met is 22 909 208 046 480 (seed 157521241); the longest run before a known value or cycle
   is 90 applications of sigma∘phi (seed 448181, which climbs to 1 100 946 774 480). Seeds <= 20000 reach 22 cycles (certificate/cycles.out), among them the fixed points
   3, 15, 255 (2^(2^k) - 1 for products of Fermat primes) and 28, 744.
2. *a(n) -> infinity (A036845 second conjecture), exact finite version.* For v = 10^3, 3·10^3, 10^4, 3·10^4, 10^5
   the set {n : a(n) <= v} is finite and computed exactly: it has 2783, 14190, 42203, 144709, 313211 elements with
   largest element 10020, 85458, 287220, 1282110, 2380164. So a(n) > 10^5 for every n > 2 380 164.
3. *Reduction.* {n : a(n) <= v} is the closure of {1, ..., v} under alternating preimages of phi and sigma (both
   finite-to-one). By König's lemma, a(n) -> infinity iff every such closure is finite iff there is no infinite
   chain x_0 <= v, x_1, x_2, ... of distinct numbers in which each x_j is the image of x_{j+1} under phi or
   sigma, the two maps alternating as in the iteration.

**Method.** (1) tug.c: phi and sigma by trial division and Pollard rho on 64-bit integers (overflow guarded),
cycle detection per seed, memo of the (min, max) of every orbit value; reproduces both b-files exactly.
(2) backward.py: breadth-first closure under exact inverse totient and inverse sigma (both checked against sieve
tables for all m < 3000); its sets agree with the b-file for v <= 1000 on n <= 16384.

**Evidence.** [`certificate/tug.c`](certificate/tug.c) (output in certificate/tug.out),
[`certificate/backward.py`](certificate/backward.py) (certificate/backward.out),
[`certificate/cycles.py`](certificate/cycles.py) (certificate/cycles.out). Lean: none. Outside Lean: all of it.

**Named problem.** Eventual periodicity of the alternating phi/sigma iteration is the question in Guy, Unsolved
Problems in Number Theory, B41; open. Details and the missing tool: scan work/OEIS-A036845/REPORT.md.

**Review level.** `rechecked` (b-files reproduced; inverse functions checked against sieves).

**Prior art.** Checked 2026-11-07: OEIS A036845, A066437, A036840 (tug-of-war family), web search (no proof),
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (no entry).
