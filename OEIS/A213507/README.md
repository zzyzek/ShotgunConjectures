# OEIS A213507: a(n) is never divisible by 2, 5, 13, 29, 31, 37, 41, 43, 53, 71, 97

**Source.** [A213507](https://oeis.org/A213507) (Hanna, 2012): e.g.f. exp(sum_{n>=1} Catalan(n) x^n/n); a = 1, 1, 3,
17, 149, 1809, ... Comment: "Conjecture: a(n) is not divisible by {2,5,13,29,31,37,41,43,53,71,97}." Formulas added
by Peter Bala (Aug 16 2026): e.g.f. C(x)^2 exp(-x C(x)^2), C the Catalan g.f., and a(n+k) - (-1)^k a(n) = 0 (mod k).
(OEIS text checked 2026-11-06.)

**Result.** True. For every listed prime p, a(n) mod p is periodic with period dividing 2p and a(n+p) = -a(n) (mod p);
a(0), ..., a(p-1) are nonzero mod p, so no a(n) is divisible by p.

**Argument.**
1. E.g.f. With C = 1 + xC^2 and D = x d/dx: D log(C^2 exp(-xC^2)) = 2xC'/C - xC^2 - 2x^2 C C'. From
   C' = C^2/(1 - 2xC), xC^2 = C - 1 and 1 - 2xC = (2 - C)/C this equals xC^2 = C - 1 = sum_{n>=1} Catalan(n) x^n,
   so exp(sum Catalan(n) x^n/n) = C^2 exp(-xC^2).
2. Congruence. Bala's theorem (2017 note, Theorem 1 and Lemma 1): if the e.g.f. of b is F(y) exp(y H(y)) with
   F, H in Z[[y]] and H(0) = 1, then b(n+k) = b(n) (mod k) for all n, k. Put y = -x, b(n) = (-1)^n a(n):
   F(y) = C(-y)^2 and H(y) = C(-y)^2 are integral with H(0) = 1, so a(n+k) = (-1)^k a(n) (mod k).
3. Finite check. With k = p: a(n+p) = -a(n) (mod p), so it suffices that p does not divide a(0), ..., a(p-1); this holds
   for all eleven primes (certificate). (For p = 2: a(n+2) = a(n) mod 2 and a(0) = a(1) = 1.)

**Evidence.**
- [`certificate/check.gp`](certificate/check.gp) (gp 2.15.4, `-D recover=0`, exit 0, no errors): the e.g.f. identity
  to O(x^400), the congruence for all n + k < 400 (0 failures), and for each prime no zero among a(0..2p-1) mod p
  with the 2p-periodicity visible; output in `certificate/out.txt`.
- Lean: none. Outside Lean: steps 1-3 (step 2 is Bala's published induction; a Lean proof would formalise the
  recurrence a(n+1) = sum_j n!/(n-j)! Catalan(j+1) a(n-j) and Bala's Lemma 1/Theorem 1, or a per-prime
  finite-state periodicity check of that recurrence).

**Review level.** `rechecked` (argument re-derived, numerics).

**Prior art.** Checked 2026-11-06: Bala's formulas in the entry (2026) and P. Bala, "Integer sequences that become
periodic on reduction modulo k for all k" (2017, linked from A047974), whose Theorem 1 gives the congruence; the
entry does not draw the conclusion for the listed primes. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.
