# OEIS A085057: the least integer ratio of two n-element products from {1..2n} is the squarefree part of (2n)!

**Source.** [A085057](https://oeis.org/A085057): a(n) is the smallest integer of the form a*b*c.../(p*q*r...),
numerator and denominator n numbers each, together all of 1..2n. "a(n) is bounded below by the squarefree part
of (2n)! and above by C(2n, n). ... That happens for all of the first 3400 terms, anyway." "Conjecture: a(n)
always equals that lower bound. - Don Reble, Jul 01 2003". Cross-reference: conjectured equal to A069113 (squarefree
part of C(2n,n)). (OEIS text, CC BY-SA 4.0, fetched 2026-11-07.)

**Result.** True for every n >= 1: a(n) = s(n), the squarefree part of (2n)! (equivalently of C(2n,n)), so also
A085057 = A069113.

**Argument.** Lower bound (entry): if r = prod A / prod B is an integer then r (prod B)^2 = (2n)!, so r = s m^2.
Construction. Start with A = {n+1..2n}, B = {1..n}, ratio C(2n,n). Swapping a top element bq in A with a bottom
element b in B (q prime, b <= n < bq) divides the ratio by q^2 and keeps |A| = n. Let v_q = v_q(C(2n,n)) and
k_q = floor(v_q/2). If we make k_q such swaps for every prime q, all with distinct elements, the ratio becomes
Prod q^(v_q mod 2) = s(n). By Legendre, q^(v_q) <= 2n, so k_q >= 1 only for q <= X = sqrt(2n), and k_q <= 1 for
q > N^(1/4), N = 2n.
Greedy: treat the primes q <= X in decreasing order; for q take k_q values b in I_q = (n/q, 2n/q] with b and bq
not used before. |I_q| >= n/q - 1, and each used element u excludes at most one b (b = u if u <= n, b = u/q if
u > n). So the greedy succeeds if |I_q| >= |U| + k_q, U = elements used for primes above q.
- N^(1/4) < q <= X: |U| <= 2 #{odd numbers in (q, X]} <= X - q + 2 and k_q <= 1. Since n/q + q >= 2 sqrt(n) =
  sqrt(2) X, the condition n/q - 1 >= X - q + 3 holds once (sqrt(2) - 1) X >= 4, i.e. n >= 47.
- q <= N^(1/4): |I_q| >= N^(3/4)/2 - 1, while |U| + k_q <= 2 pi(X) + N^(1/4) log2 N + (log2 N)/2 <=
  X + 2 + N^(1/4) log2 N + (log2 N)/2 (pi(X) <= X/2 + 1). The ratio of the right side plus 1 to N^(3/4) is
  decreasing in N and equals 0.423 < 1/2 at N = 2000, so the condition holds for n >= 1000.
For n < 1000 the greedy is run directly (it succeeds for all n <= 100000 in fact).

**Evidence.** [`certificate/greedy.py`](certificate/greedy.py) (`python3 greedy.py 1000 100000`, output
[`certificate/greedy_1e5.txt`](certificate/greedy_1e5.txt)): the greedy succeeds for every n <= 100000, and for
n <= 1000 the exponent of every prime in prod A / prod B is recomputed and equals v_p((2n)!) mod 2. The two inequalities were also evaluated
for every N in [2000, 2*10^6). Lean: none. Outside Lean: the whole argument (elementary; pi(X) <= X/2 + 1 only).

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07. The entry (and A069113) state the conjecture with the 3400-term check; web
search found no proof. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones,
2026-11-06).
