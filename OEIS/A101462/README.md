# OEIS A101462: 2^k − 509203 is never prime, so a(42228) does not exist

**Source.** [A101462](https://oeis.org/A101462) (smallest k with 2^k − prime(n) prime), comment:
"Conjecture: sequence is defined for all n. First unproved n: 286 ..." (OEIS text, CC BY-SA 4.0.)

**Result.** False: prime(42228) = 509203 and 2^k − 509203 is never prime.

**Argument.** 509203 is Riesel's number (509203·2^n − 1 is always composite); the same covering works for
2^k − 509203. Classes mod 24: 3 | 2^k − 509203 for k even, 5 for k ≡ 3 (mod 4), 7 for k ≡ 1 (mod 3),
13 for k ≡ 5 (mod 12), 17 for k ≡ 1 (mod 8), 241 for k ≡ 21 (mod 24); these cover all k. For k ≤ 18 the
value is negative, and for k ≥ 19 it is ≥ 15085 > 241.

**Evidence.**
- Lean: [`A101462.lean`](A101462.lean): for every k ≥ 19 a covering prime divides 2^k − 509203 and is
  smaller; 509203 is prime (trial division to 730).
- Lean + Mathlib: [`A101462_mathlib.lean`](A101462_mathlib.lean), `A101462_main`: `Nat.nth Nat.Prime 42227 = 509203`
  (prime(42228), 1-indexed; `Nat.count Nat.Prime 509203 = 42227` by kernel evaluation, k prime iff
  gcd(k, ∏ primes < 714) = 1 for 710 ≤ k < 714^2) and 2^k − prime(42228) is never prime;
  `A101462_conjecture_false`. Outside Lean: nothing.
- `certificate/check.py` (sieve for π(509203), direct check k ≤ 3000); `covering.gp` (scan search).

**Review level.** `lean-proof`: the index and the covering, both in [`A101462_mathlib.lean`](A101462_mathlib.lean).
**Prior art.** Known: that |2^n - 509203| is composite for all n is stated for dual Riesel numbers ([Wikipedia](https://en.wikipedia.org/wiki/Riesel_number); covering set in [Prime-Wiki](https://rieselprime.de/ziki/Riesel_prime_2_509203)). Nobody has linked it to A101462, which still has the conjecture. Searched OEIS entry, references and history, web. Checked 2026-11-04.
