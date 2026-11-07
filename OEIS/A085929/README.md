# OEIS A085929: infinitely many signatures occur on consecutive integers (known theorem); the all-signature claim is open

**Source.** [A085929](https://oeis.org/A085929): smaller of two consecutive numbers with the same prime signature
not occurring earlier. "Conjecture: (1) The sequence is infinite. (2) For every prime signature other than perfect
powers, there exists a number k such that k+1 also has the same prime signature." Joseph Myers (2004): up to
3*10^8 all terms have a signature with some exponent 1 (for example p^2*q^3 does not appear). (OEIS text,
CC BY-SA 4.0, fetched 2026-11-07.)

**Result (partial).**
- (1) True. Goldston, Graham, Pintz and Yildirim (IMRN 2011, arXiv:0803.2636, Section 2, after the proof of
  Theorem 4) prove that for every B >= 2 there are infinitely many x such that x and x+1 both have exponent
  pattern {2, 1, 1, 1, B-1}. These patterns are pairwise distinct, so infinitely many signatures occur on
  consecutive integers, and each contributes a term to A085929.
- (2) Open. New computation: no two consecutive powerful numbers up to 10^15 have the same signature (25
  consecutive powerful pairs, all with different signatures). So every signature with all exponents >= 2 (for
  example p^2 q^3) first occurs on a consecutive pair, if at all, above 10^15 (Myers: 3*10^8).
- (2) holds for every signature containing {2, 1, 1, 1} (that is {2,1,1,1} united with any multiset mu), by
  GGPY's method: adjoin to each of their three forms 3m+2, 4m+3, 10m+7 (multipliers r = 5, 7^2, 11^2) a further
  factor s_i, the s_i pairwise coprime, built from primes >= 13, all with signature mu. Each of the three
  relations then pairs numbers of signature {2,1} + mu + (E2 part {1,1}). Admissibility: the forms stay reduced
  (choose the CRT residue k with L_i(k)/(r_i s_i) coprime to r_i s_i), at p = 2, 3 the value K(m) = 1 mod 6
  gives L1 L2 L3 = 5*7*17, and for p >= 5 three forms have at most 3 < p roots. Paper argument only; GGPY state
  the case mu = {B-1}.
- Conditional: Dickson's conjecture for two linear forms implies (2) for every signature containing an
  exponent 1 (argument below).

**Argument for the conditional part.** Let the signature be {e_1, ..., e_r, 1}. Take distinct primes
2 = p_1, p_2, ..., p_r and q_1, ..., q_r, all different, A = Prod p_i^{e_i} (even), B = Prod q_i^{e_i} (odd).
Solve A P + 1 = B Q: P = P0 + B t, Q = Q0 + A t with A P0 + 1 = B Q0. The forms Bt + P0 and At + Q0 are
admissible (Q0 is odd; for each odd prime l each form has at most one root mod l). Dickson's conjecture gives
infinitely many t with both values prime and larger than all p_i, q_i; then x = A P and x+1 = B Q both have the
signature {e_1, ..., e_r, 1}.

**Evidence.** [`certificate/powerful.py`](certificate/powerful.py) (output
[`certificate/powerful_1e15.txt`](certificate/powerful_1e15.txt)): all 68575557 powerful numbers up to 10^15
(as a^2 b^3, b squarefree), sorted; 25 adjacent pairs, none with equal signatures.
[`certificate/search.py`](certificate/search.py): for primes b, d < 400 the solutions of d U^2 - b V^2 = +-1
(eta0 eps^j, j < 60) with d | U, b | V never give U/d and V/b both prime (pairs a^2 b^3, c^2 d^3 at distance 1).
Lean: none. Outside Lean: GGPY's theorem for (1); (2) is open.

**Review level.** `rechecked` (GGPY statement read in the arXiv text; computations reproducible).

**Prior art.** Checked 2026-11-07. GGPY (arXiv:0803.2636) Theorem 4 and the remark on {2,1,1,1,B-1}; the 2021
follow-up (Goldston, Graham, Panidapu, Pintz, Schettler) on x, x+n. The entry does not cite them. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).
