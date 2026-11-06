# OEIS A182484: the product is a square for p = 63, so "square iff prime" is false

**Source.** OEIS [A182484](https://oeis.org/A182484): a(n) = Product_{k=1..p-1} k^(2k-p-1), p = prime(n)
(Michel Lagneau, May 01 2012). The conjecture list (OEIS wiki, Talk:Conjectures/List) records:
"a(n) = Product_{k=1..p-1} k^(2k-p-1) is a perfect square if, and only if p = prime(n)." The entry itself
marks this conjecture false, with John W. Layman's counterexample p = 63 (May 01 2012). (OEIS text, CC BY-SA 4.0,
checked 2026-11-06.)

**Reading.** For any integer p >= 2 set P(p) = Product_{k=1..p-1} k^(2k-p-1), a positive rational. "Perfect
square" means the square of an integer.

**Result.** False as stated. P(63) = r^2 for an integer r of 348 digits, and 63 = 7 * 9. For p < 400 the
composite p with P(p) a square are 63, 105, 165, 175, 195, 273, 275, 297, 315, 351, 357, 385, 399; every prime
p < 400 gives a square (certificate/check.py). The "if" half is true for all primes (argument below; not in Lean).

**Argument.** Counterexample: compute num(63) = Product_{k>=32} k^(2k-64) and den(63) = Product_{k<32}
k^(64-2k); then num(63) = r^2 den(63) with the r in the Lean file.

"If" half (outside Lean). For odd p every exponent 2k-p-1 is even, so P(p) = R(p)^2 with
R(p) = Product k^(k-(p+1)/2), and P(p) is an integer square iff R(p) is an integer. For a prime q, Legendre
counting gives v_q(R(p)) = (1/2) Sum_{j>=1} M_j (q^j (M_j + 1) - p - 1) with M_j = floor((p-1)/q^j), since the
multiples q^j m, m <= M_j, contribute Sum (2 q^j m - p - 1) = M_j (q^j (M_j+1) - p - 1). Each factor
q^j (M_j + 1) exceeds p - 1. For p prime it is not p (p would have the proper factor q^j), so it is >= p + 1 and
every term is >= 0. For composite p the terms with q^j | p are -M_j / 2 < 0, and P(p) is a square exactly when the
other terms outweigh them; at p = 63, q = 3 gives -10 - 3 + 17 = 4
and q = 7 gives -4 + 17 = 13. (Even p >= 4 never gave a square below 400; even p is composite anyway.)

**Evidence.**
- Lean (core): [`A182484.lean`](A182484.lean). `A182484.sq63 : num 63 = r63 ^ 2 * den 63` by kernel `decide`
  (GMP-accelerated Nat arithmetic); `A182484.counterexample` packages it with 63 = 7 * 9. No axioms.
- [`certificate/check.py`](certificate/check.py): exact rational products for p = 2..399, compares
  "is an integer square" with primality.
- Outside Lean: the "if" half for primes (not needed for the disproof); the reading of P(p) as num/den.

**Review level.** `lean-witness` (the disproof is complete in Lean).

**Prior art.** Checked 2026-11-06. The OEIS entry marks the conjecture false with Layman's p = 63 (May 2012);
integrality of a(n) for primes is Problem A13 of Vandendriessche and Lee, *Problems in Elementary Number Theory*
(cited in the entry). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (no file for 182484).
