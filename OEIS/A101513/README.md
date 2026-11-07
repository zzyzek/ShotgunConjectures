# OEIS A101513: Sloane's five conjectures on the prime-sharing triangle hold

**Source.** [A101513](https://oeis.org/A101513): a(1) = 1, a(2) = 2, a(3) = 3; triangle whose n-th row holds the
n smallest positive integers not yet in the sequence that share a prime factor with some element of row n-1.
Conjectures of N. J. A. Sloane (Apr 22 2005), with "postponed" meaning "cannot be placed right away" (coprime to
the previous row): (1) n >= 4 is postponed iff n is prime; (2) every number appears; (3) the primes appear in
order; (4) 2p appears in one row and p in the next; (5) with c(i) the i-th nonprime (A018252), k(3) = 4 and
n(n+1)/2 = pi(floor(c(k(n-1))/2)) + k(n), the last term of row n is c(k(n)). (Entry checked 2026-11-07.)

**Result.** All five conjectures are true (and the sequence is a permutation of the positive integers).

**Argument.** Let R_n be the largest composite in row n and P_n = {p prime : 2p in row n-1}. Claim (I): for n >= 5,
row n = P_n ∪ {all composites in (R_{n-1}, R_n]}, i.e. P_n together with the next n - |P_n| composites after R_{n-1}.

*Step (I) at n, given (I) for earlier rows.* All composites <= R_{n-1} are used; a prime p is used iff 2p <= R_{n-2}.
- An unused p <= R_{n-1} qualifies iff a multiple of p lies in row n-1. The primes of row n-1 are smaller than p;
  its composites fill (R_{n-2}, R_{n-1}], which contains a multiple of p iff 2p <= R_{n-1}. So the qualifying
  unused numbers below R_{n-1} are exactly P_n, and they come first.
- A prime above R_{n-1} divides no element of row n-1, so it never qualifies now.
- A composite c above R_{n-1} with smallest prime factor q qualifies whenever q <= l_{n-1} = R_{n-1} - R_{n-2}:
  the interval (R_{n-2}, R_{n-1}] then contains a multiple tq with t >= 2, a composite of row n-1.
  Since q <= sqrt(R_n), it suffices that l_{n-1}^2 >= R_n.

*The inequality.* An interval of length l above 7 contains at most 48 ceil(l/210) integers prime to 210, hence at
least (162/210) l - 48 composites. Row j has at most j composites, so l_j <= (210/162)(j + 48) and
R_n <= R_{n0} + (210/162) sum_{n0 < j <= n} (j + 48). The primes of P_{n-1} lie in an interval of length l_{n-2}/2,
so |P_{n-1}| <= (24/162)(n + 46) + 48 and l_{n-1} >= (n - 1) - |P_{n-1}| >= n - 49 - (24/162)(n + 46).
With n0 = 6000 and R_6000 = 18568221 the inequality l_{n-1}^2 >= R_n holds at n = 6001 and the difference
grows with n (certificate/tail_ineq.py, exact rationals). Rows 5..6000 satisfy (I) by direct simulation of the
definition (certificate/rows.c); rows 1..4 are 1 | 2 3 | 4 6 8 | 9 10 12 14.

*Conclusions.* (1) composites are placed in the row whose interval contains them, never postponed; a prime p >= 5
is placed only after 2p, so it is postponed (2p > p and the composites near p are placed before 2p). (2) every
composite lies in some interval, every prime p follows 2p. (3) and (4) from P_n = {p : 2p in row n-1}.
(5) through row n the used numbers are the nonprimes <= R_n (including 1) and the primes p with 2p <= R_{n-1};
counting gives n(n+1)/2 = k(n) + pi(floor(R_{n-1}/2)) with R_n = c(k(n)) the last term of row n.

**Evidence.**
- [`certificate/rows.c`](certificate/rows.c): simulates the definition and checks (I) for rows 5..6000 (every prime
  in row n has 2p in row n-1, every such p is in row n, the composites of row n are exactly those in
  (R_{n-1}, R_n]); [`rows6000.out`](certificate/rows6000.out). The first 72 terms equal the entry's data.
- [`certificate/tail_ineq.py`](certificate/tail_ineq.py): the inequality for n > 6000.
- Lean: none. Outside Lean: the whole argument (simulation of rows 5..6000 and the paper induction).

**Review level.** `agent`.

**Prior art.** OEIS A101513, A104655, A104656 (conjectures still listed), google-deepmind/formal-conjectures (no
file), otoi-lab/oeis-lean-proofs (none); 2026-11-07. The invariant and the sieve induction are ours.
