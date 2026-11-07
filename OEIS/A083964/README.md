# OEIS A083964: a(n) != 0 when 5 does not divide 2n - 1

**Source.** [A083964](https://oeis.org/A083964) (Amarnath Murthy and Meenakshi Srikanth, May 20 2003): smallest
palindromic multiple of 2n - 1 beginning with the digit string of 2n - 1, or 0 if none exists. "Conjecture: If n is
not of the type (5k+1)/2 then a(n) is not zero." A comment by Lars Blomberg (Sep 22 2013) proves more: with
k = 2n - 1 of c digits, a(n) != 0 iff gcd(k, 10^c) divides reverse(k), using the theorem of Harminc and Sotak that an
arithmetic progression a0 + i d contains palindromes unless 10 divides both a0 and d. (OEIS text, CC BY-SA 4.0,
revision #25, checked 2026-11-07.)

**Reading.** n is of the form (5j + 1)/2 exactly when 5 | 2n - 1. A palindrome begins with the digits of k iff it ends
with the digits of rev(k) (k reversed; k is odd, so rev(k) has c digits).

**Result.** True (known, Blomberg 2013). Here with a self-contained elementary proof of Blomberg's full criterion:
for n >= 1, a(n) != 0 iff gcd(k, 10^c) divides rev(k).

**Argument.** Let k = 2n - 1 with digit string s.
1. *Construction.* Write k = g m with gcd(m, 10) = 1 and suppose g | rev(k) (always true for g = 1, i.e. 5 does not
   divide k). Let Y = s rev(s), a palindrome with value k 10^c + rev(k), divisible by g. Repeat Y j + 2 times; the
   result P is a palindrome beginning with s and P = Y (1 + 10^|Y| + ... ), and by Euler's theorem the base-10^|Y|
   repunit factor is divisible by m for j + 2 = 2 phi(m (10^|Y| - 1)). So k | P.
2. *Necessity.* If P is such a palindrome then P = rev(k) + 10^c X, so gcd(k, 10^c) | rev(k).
3. *Sufficiency in general.* Let k = 5^v m (k is odd) and suppose gcd(k, 10^c) | rev(k); then
   gcd(5^v, 10^c) | rev(k), so 10^c x == -rev(k) (mod 5^v) has a solution x < 5^v. Put the palindromic block
   X rev(X) (X = digits of x padded to v places) between s and rev(s): Y = s X rev(X) rev(s) has value
   rev(k) + 10^c x + 10^(c+v)(...), divisible by 5^v. Repeating Y as in step 1 handles m.

**Evidence.**
- Lean (Mathlib): [`A083964_mathlib.lean`](A083964_mathlib.lean). Main theorem `A083964.A083964_main : 1 ≤ n →
  ¬ 5 ∣ 2n - 1 → ∃ P, 0 < P ∧ (2n - 1) ∣ P ∧ IsPal P ∧ BeginsWith (2n - 1) P`; also `A083964_zero` (step 2) and
  `A083964_nonzero_of` (step 3, first case). Euler step: `dvd_rep` from `OpenProblemsLib.Digits10`. Check:
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. No `sorry`, no
  `native_decide`.
- [`certificate/check.py`](certificate/check.py): brute force reproduces the data for n <= 40; the zero criterion
  matches Blomberg's for n <= 4090.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: the entry's own comment (Blomberg 2013, via M. Harminc, R. Sotak, Palindromic numbers
in arithmetic progressions, Fibonacci Quart. 36 (1998) 259-262) settles the conjecture and the full criterion.
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones 2026-11-06). Same repetition
construction as [A084043](../A084043/README.md).
