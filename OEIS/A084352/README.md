# OEIS A084352: the minimum digit of the factors of a palindromic brilliant number is never greater than 3

**Source.** [A084352](https://oeis.org/A084352) (Jason Earls, Jun 22 2003): minimum digit of the two prime factors
of the palindromic brilliant numbers (semiprimes p q whose prime factors have the same number of digits, e.g.
989 = 23 * 43). "Conjecture: a(n) is never greater than 3." (OEIS text, CC BY-SA 4.0, revision #11, checked
2026-11-07.)

**Result.** True, and sharper: a(n) = 3 only for 9 = 3 * 3 (n = 3); a(n) <= 2 for every other n. The factors need
not be palindromes.

**Argument.** Let p, q be primes with the same number d of digits, all digits >= 3, (p, q) != (3, 3). By step 1 of
[A084189](../A084189/README.md) the product has exactly 2d digits, an even number. An even-length palindrome is
divisible by 11, so 11 | pq and p = 11 or q = 11, which has digit 1. So pq is not a palindrome. (For d = 1:
3 * 3 = 9 is the one palindrome; 3 * 5, 3 * 7, 5 * 5, 5 * 7, 7 * 7 are not.)

**Evidence.**
- Lean (Mathlib): [`../A084189/A084189_mathlib.lean`](../A084189/A084189_mathlib.lean), theorems
  `A084189.A084352_main` (digits >= 4, equal digit counts: p * q not a palindrome) and `A084189.A084352_sharp`
  (digits >= 3: p * q palindrome forces p = q = 3). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms
  propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- Outside Lean: none.
- [`certificate/brill.c`](certificate/brill.c): direct search over all pairs of d-digit primes with digits >= 4,
  d <= 7: no palindromic product (as the proof predicts).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: OEIS A084352 and A078972, web search, google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs local clones (2026-11-06): no proof found. Immediate from the classical
11-divisibility of even-length palindromes.
