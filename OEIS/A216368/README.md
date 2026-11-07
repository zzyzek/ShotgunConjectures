# OEIS A216368: the n-th derivative separates all towers for n <= 19 (partial)

**Source.** [A216368](https://oeis.org/A216368): T(n,k) = number of distinct values of the k-th derivative at x = 1
of x^x^...^x (n x's, all parenthesizations). Conjecture (entry): "T(n,n) = A000081(n) for n>=1. It would be nice
to have a proof (or a disproof if the conjecture is wrong)." Rows n <= 16 in the b-file (A. P. Heinz).
(Entry checked 2026-11-07.)

**Reading.** The functions are indexed by rooted trees with n nodes: a node is x raised to the product of its
children's functions ((a^b)^c = a^(bc)); A000081(n) is the number of trees.

**Result (partial).** T(n,n) = A000081(n) for every n <= 19 (three rows beyond the b-file); the general statement
stays open (see the obstruction report in the scan repository, work/OEIS-A216368/REPORT.md).
New rows (k = 1..n):
- n = 17: 1 16 95 684 5297 35316 171734 384582 518519 598279 625063 632551 634461 634801 634844 634847 634847
- n = 18: 1 17 107 822 6834 52755 309508 859641 1273255 1567122 1674932 1708421 1718349 1720727 1721109 1721156
  1721159 1721159
- n = 19: 1 18 119 985 8635 76517 521813 1839861 3030323 4075071 4487746 4625799 4672668 4685493 4688193 4688625 4688673 4688676 4688676

**Argument.** f^(k)(1) is computed exactly modulo p = 2^64 - 59 by f = exp(u), u = G log x:
u^(k) = sum_j C(k,j) G^(j)(1) L_(k-j) with L_m = (-1)^(m-1) (m-1)!, and f^(k+1) = sum_j C(k,j) u^(j+1) f^(k-j),
G the product of the children's functions (Leibniz rule). Distinct residues mod p imply distinct integers, so a
count of distinct residues is a lower bound for T(n,k); it equals A000081(n) for k = n at n = 17, 18, 19 (634847, 1721159 and 4688676 trees), which is
also the upper bound. For k < n the n = 17, 18, 19 entries are lower bounds that are exact unless two true values
collide mod p (entries equal to A000081(n) are exact).

**Evidence.**
- [`certificate/towers.c`](certificate/towers.c), [`towers18_p1.out`](certificate/towers18_p1.out) (rows 1..18), [`towers19_p1.out`](certificate/towers19_p1.out) (rows 1..19);
  rows 1..16 equal the b-file [`b216368.txt`](certificate/b216368.txt) entry by entry.
- Lean: none. Outside Lean: the computation.

**Review level.** `agent`.

**Prior art.** OEIS A216368 (conjecture open, b-file to n = 16), google-deepmind/formal-conjectures (no file),
otoi-lab/oeis-lean-proofs (none); 2026-11-07.
