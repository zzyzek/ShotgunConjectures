# OEIS A084043 and A084044: a(n) = 0 iff 10 divides n

**Source.** [A084043](https://oeis.org/A084043) (Amarnath Murthy, 2003): smallest palindromic multiple of n in
which the digit string of n appears "sandwiched between at least a pair of digits", or 0 if none exists.
[A084044](https://oeis.org/A084044) (Murthy and Meenakshi Srikanth, 2003): smallest palindromic multiple of n in
which n is a substring anywhere, or 0. Both: "Conjecture: a(n) = 0 iff n = 10k." (OEIS text, CC BY-SA 4.0, A084043
revision #5 of Dec 05 2013, A084044 revision #7 of Aug 23 2014, checked 2026-11-06.)

**Result.** True for both: for n >= 1 a palindromic multiple of n containing n with a digit on each side exists iff
10 does not divide n (hence also one containing n anywhere).

**Argument.**
1. *10 | n.* A positive multiple of 10 ends in 0; a palindrome would then start with 0. No such multiple exists.
2. *10 does not divide n.* Write n = g m with g = 2^a 5^b and gcd(m, 10) = 1. Let e = a + b + 1, so g | 10^e and
   g < 10^e; let E be the decimal string of g padded with leading zeros to length e. Since 10 does not divide
   g, the last digit of g is nonzero. Let s be the decimal string of n and
   Y = rev(E) s rev(s) E (a palindrome whose first digit is the last digit of g, nonzero, and whose value is
   g mod 10^e, hence divisible by g). Let L = |Y|, M = m (10^L - 1), k = 2 phi(M) >= 2, and P = Y repeated k
   times. P is a palindrome, P = Y (1 + 10^L + ... + 10^{L(k-1)}), and 10^{Lk} == 1 (mod M) by Euler (10^L is
   coprime to m and to 10^L - 1), so m divides the repunit factor; g divides Y. So n | P, and the copy of s in the
   second block of P has digits on both sides.

**Evidence.**
- Lean (Mathlib): [`A084043_mathlib.lean`](A084043_mathlib.lean). Digit strings are `Nat.digits 10` (least
  significant first; reversal preserves palindromes and substrings). Main theorems
  `A084043.A084043_main : 0 < n → ((∃ P, 0 < P ∧ n ∣ P ∧ IsPal P ∧ Sandwich n P) ↔ ¬ 10 ∣ n)` and
  `A084043.A084044_main` (same with `digits 10 n <:+: digits 10 P`); construction `construct`, Euler step
  `dvd_rep`, impossibility `no_pal_of_ten`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms
  propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/brute.py`](certificate/brute.py): brute-force least values reproduce the data of both entries
  (A084043 n <= 38, A084044 n <= 45); exit 0.
- Outside Lean: none. a(n) != 0 is the existence statement; the least values themselves are not proved in Lean.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Existence of palindromic multiples of every n not divisible by 10 is known
(M. Harminc, R. Sotak, Palindromic numbers in arithmetic progressions, Fibonacci Quart. 36 (1998) 259-262); the
versions requiring n itself as a (sandwiched) substring are still conjectures in both entries. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
