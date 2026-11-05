# OEIS A123722: multiples of 3 in the list are 3 and 3p (p prime), and every odd prime occurs

**Source.** OEIS [A123722](https://oeis.org/A123722) (J. W. Layman, 2006): values of n with
A000224(n) = ⌈(n+1)/3⌉, where A000224(n) is the number of squares mod n (1, 3, 4, 8, 9, 15, 21,
33, ...; offset 1). Comment: "If n>2 and a(n) is a multiple of 3, then a(n)/3 is a prime;
further, all odd primes are given as a(n)/3 for some n." (OEIS text, CC BY-SA 4.0.)

**Reading.** ⌈(n+1)/3⌉ = ⌊n/3⌋ + 1. Since a(1) = 1 and a(2) = 3, "n > 2" means a(n) > 3.

**Result.** Proved, both parts.

**Argument.** Let S(n) = A000224(n).
1. S is multiplicative on coprime arguments (Chinese remainder theorem).
2. S(m) ≤ ⌊m/2⌋ + 1 because x and m − x have the same square. If d² | m with d ≥ 2, then 0 and
   m/d also share a square (both square to 0), so S(m) ≤ ⌊m/2⌋.
3. For an odd prime p, x² ≡ y² (mod p) with 0 ≤ x, y ≤ (p−1)/2 forces x = y, so 2S(p) = p + 1.
4. Take m odd with 2S(m) = m + 1. Then m = 1 or m is prime. Otherwise let p = minFac(m). If
   p² | m, step 2 gives a contradiction. If not, m = p·b with b ≥ 2 coprime to p, and
   4S(p)S(b) ≤ (p+1)(b+1) < 2(pb+1).
5. If M | N then S(N) ≤ S(M)·N/M, since every square mod N reduces to a square mod M. With
   S(9) = 4 this gives S(3^k) ≤ 4·3^(k−2).
6. For k ≥ 3, squaring is injective on {3j+1 : j < 3^(k−1)} mod 3^k: 3^k divides
   3(i−j)(3(i+j)+2) and the last factor is prime to 3. Adding the squares 0 and 9 gives
   S(3^k) ≥ 3^(k−1) + 2.
7. Classification. Write N = 3^k·r with 3 ∤ r and S(N) = N/3 + 1.
   - k = 1: 2S(r) = r + 1. So r is odd (by parity), and step 4 gives r = 1 (N = 3) or r prime.
   - k ≥ 2 and r ≥ 4: steps 2 and 5 give 2S(N) ≤ 4·3^(k−2)(r+2) < 2·3^(k−1)r + 2.
   - k ≥ 2 and r = 2: S(N) = 2S(3^k) is even, but 2·3^(k−1) + 1 is odd.
   - k ≥ 2 and r = 1: step 6 rules out k ≥ 3, leaving N = 9 = 3·3.
8. Every odd prime occurs: S(9) = 4, and S(3p) = 2·(p+1)/2 = p + 1 for primes p ≥ 5.

The c(q^e) = q^e trap from the sibling OEIS-A123365 does not arise. Steps 5 and 6 use only
bounds valid for every exponent, never exact prime-power values.

**Evidence.**
- [`A123722_mathlib.lean`](A123722_mathlib.lean) (Mathlib). `A123722_main` proves both parts for
  a(n) = `Nat.nth` of {N > 0 : S(N) = N/3 + 1} (offset 1). `A123722_classify` is the
  classification, and `A123722_data` checks the members below 40 against the OEIS data. Axioms:
  propext, Classical.choice, Quot.sound. Outside Lean: nothing.
- `certificate/check.py` is a brute-force check of the classification (run to n < 6000).

**Review level.** lean-proof.

**Prior art (2026-11-05).** The OEIS entry still marks this as a conjecture. A web search found no
proof. google-deepmind/formal-conjectures has no file for A123722.
