# OEIS A081086: a(n+1) ≥ (3/4)·a(n)(a(n) − 1), so liminf log a(n+1)/log a(n) ≥ 2 (the limit itself is open)

**Source.** OEIS [A081086](https://oeis.org/A081086): smallest partial quotients of an infinite
simple continued fraction x = [0; a_1, a_2, …] such that the fractional remainders
[0; a_k, a_{k+1}, …] sum to 1. Conjecture: "log(a(n+1))/log(a(n)) -> 2" (OEIS text, CC BY-SA 4.0).

**Reading.** The greedy rule that reproduces all listed terms (and the stated lengths 69 and
140 of the 9th and 10th terms) is

  a_{k+1} = least a ≥ 1 with F_k(1/a) < 1, where F_k(y) = y + Σ_{j=1}^{k} [0; a_j, …, a_{k−1}, a_k + y].

F_k(1/a) is the remainder sum when the tail after a_k is the single quotient a; the tail sum is
always above its first remainder, so a must leave room below 1.

**Result.**
1. For every k ≥ 2: (3/4)·a_k(a_k − 1) − 1 < a_{k+1} ≤ 1/r_k + 1, where
   r_k = 1 − F_{k−1}(1/a_k) > 0 is the deficit left after a_k (a rational number).
   Hence liminf log a_{k+1}/log a_k ≥ 2.
2. The conjecture is equivalent to r_k = a_k^{−2+o(1)}, i.e. log(1/(r_k a_k²)) = o(log a_k).
   The only unconditional lower bound found is r_k ≥ 1/lcm(Q_1, …, Q_k) with
   Q_j = K(a_j, …, a_k) the continuants, which gives log a_{k+1} ≤ (2k − 2 + o(1)) log a_k.
3. Terms a_1 … a_15 computed (a_15 has 4455 digits). D_k = ln(a_{k+1}/a_k²) for k = 2 … 14 is
   0.81, 0.12, 0.54, 0.22, 0.26, 0.60, 1.81, 2.45, 0.35, 0.06, 0.64, 0.03, 0.99, so the ratio
   log a_{k+1}/log a_k is 2.0002 at k = 14.

**Argument.** Write G(z) = z + Σ_{j<k} X_j(z) with X_{k−1}(z) = 1/(a_{k−1} + z),
X_j = 1/(a_j + X_{j+1}), so F_{k−1}(z) = G(z) and F_k(y) = G(1/(a_k + y)) + y. All a_i ≥ 2, so
every X_i ≤ 1/2 and |dX_j/dz| = ∏_{i=j}^{k−1} X_i² ≤ 4^{−(k−j)}; hence G is increasing with
slope in [2/3, 4/3] on (0, 1].
Minimality of a_k gives G(1/(a_k − 1)) ≥ 1, while G(1/a_k) = 1 − r_k, so
r_k ≤ (4/3)(1/(a_k − 1) − 1/a_k) = (4/3)/(a_k(a_k − 1)).
For the next quotient, G(1/(a_k + 1/a)) ≥ G(1/a_k) − (4/3)(1/a)/a_k², so
F_k(1/a) ≥ 1 − r_k + (1/a)(1 − 4/(3a_k²)); F_k(1/a) < 1 forces
a > (1 − 4/(3a_k²))/r_k ≥ (3/4)a_k(a_k − 1) − 1. Conversely G is increasing, so
F_k(1/a) ≤ 1 − r_k + 1/a < 1 once a > 1/r_k. The rational r_k has denominator dividing
lcm(Q_1..Q_k) since [0; a_j, …, a_k] = Q_{j+1}/Q_j; with Q_j ≤ ∏_{i≥j}(a_i + 1) this gives part 2's
bound. Equivalence in part 2: a_{k+1} = r_k^{−1}·(1 + O(1/a_k²)) up to an additive 1.

**Evidence.** No Lean. Outside Lean: the inequalities above (paper proof) and the computation
`certificate/cf2.py` (exact rationals; checks minimality of each a_k, reproduces the 9 listed terms,
output `certificate/cf2.out`, terms `certificate/A081086_terms.txt`).

**Review level.** `rechecked` (paper proof; inequality checked on all 15 terms).

**Prior art.** OEIS A081086 (checked 2026-11-07) lists the conjecture only; google-deepmind/formal-conjectures
and otoi-lab/oeis-lean-proofs have no entry. Status: open. The obstruction is Diophantine: the
conjecture needs the deficit r_k not to be much smaller than 1/a_k², a "no exceptionally good
cancellation" property of a self-defined real sequence, of the same type as bounding the
irrationality measure of a specific number.
