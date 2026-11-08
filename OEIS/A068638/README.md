# OEIS A068638: no odd term above 25 below 3.5·10^9, and none outside two residue classes

**Source.** OEIS [A068638](https://oeis.org/A068638) (a(1) = 1, a(n) = smallest distinct
composite number such that a(n) + a(k) is composite for all k = 1 to n), comment: "Conjecture:
25 is the largest odd term of this sequence." (OEIS text, CC BY-SA 4.0.) Essentially the same
as A025044.

**Result (partial; the conjecture stays open).** An odd composite x > 25 is not a term if
x < 3.5·10^9, or x ≢ 1 (mod 6), or x ≡ 1 (mod 6) with x ≢ 1 and x ≢ 25 (mod 23# = 223092870).
So any odd term after 25 lies in one of the two classes 1, 25 (mod 223092870) and exceeds
3.5·10^9.

**Argument.**
1. Structure. A number that fails the test once fails it forever (the set of earlier terms only
   grows), so the sequence is increasing and a composite y is a term iff y + s is composite for
   every term s < y. Suppose 1 and 25 are the only odd terms below x. Then an even e is a term
   iff e + 1 and e + 25 are composite (sums of two evens are even), and the odd composite x is
   rejected iff some even term e < x has x + e prime. Every even e ≥ 8 with e ≡ 2 (mod 6) is a
   term (e + 1 and e + 25 are multiples of 3 above 3). `certificate/sim.py` checks this
   description against the greedy definition up to 30 000.
2. x < 3.5·10^9 (computation, `certificate/wit.c`, segmented sieve): every odd composite
   27 ≤ x < 3.5·10^9 (1 582 720 663 numbers) has an even e ≤ 1920, e < x, with e + 1, e + 25
   composite and x + e prime.
3. x ≥ 3.47·10^9, x ≡ 3 or 5 (mod 6). By Bennett–Martin–O'Bryant–Rechnitzer (Illinois J. Math.
   62 (2018), Thm 1.1: |θ(y; q, a) − y/φ(q)| < (1/1000)(q/φ(q)) y/log y for 3 ≤ q ≤ 10^5,
   gcd(a, q) = 1, y ≥ 3.47·10^9) with q = 6 there is a prime p ≡ x + 2 (mod 6) in
   (x + 13, 2x). Then e = p − x ≡ 2 (mod 6), 14 ≤ e < x, is a term and x + e = p is prime.
4. x ≥ 3.47·10^9, x ≡ 1 (mod 6). If ℓ1 ≠ ℓ2 are primes in {5, …, 23} with x ≢ 1 (mod ℓ1)
   and x ≢ 25 (mod ℓ2), take a prime p in (x + 13, 2x) with p ≡ x (mod 6),
   p ≡ x − 1 (mod ℓ1), p ≡ x − 25 (mod ℓ2) (a reduced class mod q = 6ℓ1ℓ2 ≤ 2622; the same
   theorem gives θ(2x; q, ·) − θ(x + 13; q, ·) ≥ (x − 14 − 0.36x)/φ(q) > 0). Then e = p − x
   is even, ≥ 14, ℓ1 | e + 1 and ℓ2 | e + 25, so e is a term and x + e = p is prime. Such
   ℓ1, ℓ2 exist unless x ≡ 1 (mod ℓ) for all ℓ ∈ {5, …, 23} or x ≡ 25 (mod ℓ) for all of them
   (if only one prime were available for both roles, x would be ≡ 1 and ≡ 25 modulo the others).

**Evidence.** `certificate/wit.c` and its output `certificate/wit35.out` (step 2),
`certificate/sim.py` (step 1). No Lean: step 2 is a 3.5·10^9 sieve and steps 3–4 use the
explicit prime number theorem for progressions. Outside Lean: everything.

**Review level.** `rechecked` (structure re-derived and simulated; computation run here).

**What is missing.** The classes x ≡ 1, 25 (mod 223092870) with x ≥ 3.5·10^9: there one needs a
prime p ∈ (x + 13, 2x) with p − x + 1 and p − x + 25 composite. Either an explicit upper bound
for prime pairs p, p − h (Riesel–Vaughan type, uniform in h) or the large-modulus range of the
explicit θ(x; q, a) bounds (q ≈ 30 log x) would finish it.

**Prior art.** The entry still lists the conjecture (cached entry, 2026-11-07); A025044 has no
proof. google-deepmind/formal-conjectures (clone of 2026-11-06) and otoi-lab/oeis-lean-proofs
have no file for A068638 or A025044.
