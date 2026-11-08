# OEIS A110073: partial result on sigma(n) = 2n - phi(phi(n))

**Source.** [A110073](https://oeis.org/A110073): numbers n with σ(n) = 2n - φ(φ(n)). Comment: for odd primes p
with 8p + 1 prime, n = 10(8p + 1) is a term. Conjecture: every term greater than 76 has this form. (OEIS text,
CC BY-SA 4.0, cached entry checked 2026-11-07.)

**Result (partial; the conjecture stays open).**
1. Every solution n ≤ 10^8 other than 1, 2, 4, 10, 76 has the form 10(8p + 1), p and 8p + 1 prime (8567
   solutions; certificate/scan.c).
2. Among n of the shapes q, 2q, 4q, pq, 2pq (p < q odd primes) the solutions are exactly 2, 10, 76 and the
   10(8p + 1) family.
3. For n = 2^a q with a >= 3 (q odd prime), n is a solution iff q = 2t + 1 with t odd and
   t + 1 = 2^(a-2) (φ(t) + 4), a Lehmer-type totient equation (compare Lehmer's k φ(t) = t - 1). Such t is
   composite with at least three distinct prime factors; there is none with t <= 3·10^8 (any a).

**Argument for 2.** Use φ(m) ≤ m/2 for even m, and for odd t > 1: t - φ(t) is odd, equals 1 iff t is prime, equals
3 iff t = 9 (two distinct prime factors r < s give t - φ(t) ≥ r + s - 1 ≥ 7).
- n = q: q + 1 = 2q - φ(q - 1) forces φ(q - 1) = q - 1, so q = 2.
- n = 2q: φ(q - 1) = q - 3 ≤ (q - 1)/2, so q ≤ 5; only n = 10 works.
- n = pq odd: σ(n) ≥ 2n - (p - 1)(q - 1)/2 gives (p - 1)(q - 1) ≤ 4, impossible for 3 ≤ p < q.
- n = 4q: φ(2(q - 1)) = q - 7. Write q - 1 = 2^b t, t odd: 2^(b-1)(t - φ(t)) = 3, so b = 1, t = 9, q = 19, n = 76.
- n = 2pq: φ((p - 1)(q - 1)) = (p - 3)(q - 3) - 12. p = 3 is impossible (negative). For p ≥ 7 the bound
  φ ≤ (p - 1)(q - 1)/2 gives (p - 5)(q - 5) ≤ 32, so q ≤ 21, covered by item 1 (no solutions). For p = 5:
  φ(4(q - 1)) = 2q - 18; with q - 1 = 2^b t, t odd, this is 2^(b+1)(t - φ(t)) = 16, so b = 3 and t is prime:
  n = 10(8t + 1).

*Item 3.* σ(n) = (2^(a+1) - 1)(q + 1) and φ(φ(n)) = φ(2^(a-1)(q - 1)). Write q - 1 = 2^b t, t odd: the equation
becomes 2^(a+b-2) φ(t) = 2^b t + 2 - 2^(a+1). For b >= 2 the right side is 2 mod 4 and the left side is divisible
by 8: impossible. For b = 1 it is 2^(a-2) φ(t) = t + 1 - 2^a. t = 1 and t prime are impossible (t + 1 < 2^(a-2)(t + 3)),
and φ(t)/t < 1/2 forces three or more prime factors (two odd primes give at least 8/15).

**Evidence.**
- [`certificate/scan.c`](certificate/scan.c): sieves σ and φ to 10^8 and prints solutions outside the family
  (only 1, 2, 4, 10, 76).
- [`certificate/tot.c`](certificate/tot.c): no odd t <= 3·10^8 solves t + 1 = 2^j (φ(t) + 4), j >= 1.
- Lean: none. Outside Lean: item 2's argument (above) and the scan in item 1.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07: OEIS entry, formal-conjectures, oeis-lean-proofs: nothing beyond the entry's
own family construction. The general case is open (see the scan repo's work/OEIS-A110073/REPORT.md).
