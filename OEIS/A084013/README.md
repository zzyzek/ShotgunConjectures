# OEIS A084013 and A084015: every n has an n-digit palindromic multiple

**Source.** [A084013](https://oeis.org/A084013) (Amarnath Murthy and Meenakshi Srikanth, May 23 2003): smallest n-digit
palindromic multiple of n; "For n = 10k it is sufficient that the multiple is palindromic with leading zeros
ignored. 0 if no such number exists." [A084015](https://oeis.org/A084015) (same authors, same date): the largest
such number. Both entries: "Conjecture: no entry is zero." (OEIS text, CC BY-SA 4.0, checked 2026-11-07.)

**Reading.** Both conjectures say the same thing: for every n >= 1 an admissible n-digit multiple of n exists.
Admissible: a palindrome if 10 does not divide n; if n = 10^s n' with s >= 1 and 10 not dividing n', a number
10^s u with u a palindrome (prepending s zeros gives a palindrome). This reading reproduces the data: a(10) =
1000000010 (10^9 = 10^9 * 1 would be admissible if any number of zeros could be dropped, and it is not the term).

**Result.** True: no term of A084013 or A084015 is 0.

**Argument.** It suffices to show: (*) if 10 does not divide n' and L >= n' (and L >= 12 when n' is 2, 4 or 8),
there is an L-digit palindrome divisible by n'. For 10 not dividing n take n' = n, L = n (for n = 2, 4, 8 use 22,
2112, 21100112); for n = 10^s n' take L = n - s and N = 10^s u.

Write n' = g m with g = 2^a 5^b (a = 0 or b = 0) and gcd(m, 10) = 1.
1. *g = 1.* Let m = 3^k m' with 3 not dividing m', r = 3^k phi(m') <= m. Then 9m | 10^r - 1: 3^(k+2) | 10^(3^k) - 1
   (lifting the exponent: if x = 1 + 3^(k+2) c then x^3 - 1 = (x - 1)(x^2 + x + 1) gains a factor 3) and
   m' | 10^phi(m') - 1 (Euler). Put U = (10^r - 1)/9 (r ones). For r <= L, P = U (10^(L-r) + 1) is an L-digit
   palindrome: two copies of the run of ones, overlapping in digits 2 when L < 2r, separated by zeros otherwise; no
   carries. 9P = (10^r - 1)(10^(L-r) + 1), so m | P.
2. *g > 1.* Let e = a + b, so g | 10^e and g < 10^e; let G be the decimal string of g padded with leading zeros to
   e digits; its last digit is nonzero. Let R = e phi(m), so 10^R == 1 (mod m) and R >= e. Take the palindrome whose
   low R + e digits read (from the units digit up) G reversed, then R - e nines, then the digit complements 9 - d of G
   reversed; then zeros; then the mirror image of the low block on top. Its leading digit is the units digit of g.
   The low block has value (10^e - g)(10^R - 1) and the mirrored block (g' + 1)(10^R - 1) (g' = the number with the
   digits of G reversed), both divisible by m; the low block is == g (mod 10^e) and the top block sits above 10^e,
   so g | P. This needs 2(R + e) <= L, which holds for L >= g m because 2e <= g (for m >= 2, R + e <= e m) and
   4e <= g when m = 1, except g = 2, 4, 8, where L >= 12 is assumed.

**Evidence.**
- Lean (Mathlib): [`A084013_mathlib.lean`](A084013_mathlib.lean). Main theorem `A084013.A084013_main : 1 ≤ n → ∃ N,
  (digits 10 N).length = n ∧ n ∣ N ∧ (¬ 10 ∣ n → IsPal N) ∧ (10 ∣ n → PalLZ n N)`; steps `pal_U` and `ord_bound`
  with `lte3` (step 1), `pal_G` (step 2), `pal_exists` (*). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings;
  axioms of every theorem at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): brute force reproduces a(1..10) of both entries under the reading
  above; the construction, built explicitly, is checked for n <= 400.
- Outside Lean: none. Not proved: the least and greatest values themselves.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: OEIS A084013, A084015; web search (no proof of the exact-length statement found;
existence of some palindromic multiple of every n not divisible by 10 is Harminc-Sotak 1998, and Banks, Hart and
Sakata studied palindromes in residue classes, neither with a fixed length); google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs local clones (2026-11-06): nothing.
