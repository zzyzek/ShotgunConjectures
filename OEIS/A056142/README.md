# OEIS A056142: a(n) palindrome only if all digits of n are equal

**Source.** [A056142](https://oeis.org/A056142), Henry Bottomley, Jun 15 2000: "Concatenate n, floor[n/10],
floor[n/100] ... (but do not continue if floor[.]=0)." Comments: D. Wasserman (May 23 2005) states that for
3-digit n, a(n) is a palindrome iff n is, and for 4 or 5 digits iff all digits of n are equal; F. T. Adams-Watters
(Sep 07 2006) conjectures "if n has 3 or more digits, a(n) is a palindrome only if all the digits of n are the
same" and notes that such a palindrome uses at most 2 distinct digits. (OEIS text, CC BY-SA 4.0, revision #9 of
Jul 11 2020, checked 2026-11-06.)

**Reading.** Palindrome means the decimal string reads the same backwards (`Nat.digits 10 m` equals its reverse).
The words "3 or more" conflict with Wasserman's 3-digit comment; the intended range is 4 or more digits.

**Result.** As stated the conjecture is false: n = 101 has 3 digits and a(101) = 101101 is a palindrome (every
3-digit palindrome n is a counterexample, as Wasserman's comment already implies). For 4 or more digits it is
true: if n has d >= 4 digits, a(n) is a palindrome iff all digits of n are equal.

**Argument.** Write n = x_1 ... x_d, u_k = x_1 ... x_k and T(k) = k(k+1)/2. Then a(n) is the word
w = u_d u_(d-1) ... u_1 of length T(d), and its reverse is rev(u_1) rev(u_2) ... rev(u_d).

1. *Reduction.* If w is a palindrome, its first d letters equal those of the reverse, so for 3 <= i <= d,
   x_i = x_(T(m)+1-i) where T(m-1) < i <= T(m); the index on the right is smaller than i. Hence x is determined
   by x_1, x_2: x_i = phi(X_i), where X is the word over {a, b} with X_1 = a, X_2 = b and X_p = X_(T(m)+1-p) for
   T(m-1) < p <= T(m), and phi(a) = x_1, phi(b) = x_2. If x_1 = x_2 all digits are equal. Otherwise phi is
   injective, and the word for X_1 ... X_d must itself be a palindrome. X begins abaabaaababaab...
2. *Palindrome gives a near-square.* For the word of X_1 ... X_d the reverse is X_1 ... X_T(d) (block m of X,
   positions T(m-1)+1 .. T(m), is X_m ... X_1). Positions d+1 .. 2d-1 of w hold u_(d-1) = X_1 ... X_(d-1), so a
   palindrome gives S(d): X_(d+i) = X_i for 1 <= i <= d-1.
3. *S(r) fails for every r >= 4*, by strong induction. For r <= 105 by direct computation. For r >= 106 let K be
   such that T(K-1) < r <= T(K); block K+1 of X (positions T(K)+1 .. T(K+1)) lies in r+1 .. 2r-1. Set
   e = T(K+1) - r, so K+1 <= e <= 2K. Block K+1 is X_(K+1) ... X_1, and S(r) moves it to positions e-K .. e:
   X_t = X_(e+1-t) for 1 <= t <= K+1. Let T(k) <= e < T(k+1) and o = e - T(k), 0 <= o <= k; then
   5 <= k and 2k <= K+1. Reading block k (or block k-1 when o = 0) of X inside this mirrored copy gives
   X_t = X_(t-o) for o+1 <= t <= o+k (and X_t = X_(t-k) for k+1 <= t <= 2k-1 when o = 0). If o = 0 this is S(k);
   if o >= 4 it contains S(o); both have 4 <= index < r, contradicting the induction hypothesis. If o = 1, 2, 3 it
   gives X_2 = X_1, X_4 = X_2 or X_8 = X_5, all false (X_1 ... X_8 = abaabaaa).
4. Conversely, if all digits are equal, a(n) is a string of one repeated digit.

**Evidence.**
- Lean (Mathlib): [`A056142_mathlib.lean`](A056142_mathlib.lean). `a` is the entry's definition (n, then
  a(floor(n/10)), stopping at 0); `digits_a` relates `Nat.digits 10 (a n)` to the word `W`. Main theorems
  `A056142_conjecture : 4 ≤ (Nat.digits 10 n).length → ((Nat.digits 10 (a n)).reverse = Nat.digits 10 (a n) ↔
  ∃ c, Nat.digits 10 n = List.replicate (Nat.digits 10 n).length c)` and `A056142_three_digits_false`
  (n = 101). Route: `word_reduction`, `fp_unique` (step 1), `X_block`, `RR_cw`, `S_of_pal` (step 2), `not_S` with
  `S_base` (kernel `decide` for r < 106) and `X_vals` (step 3). Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check_A056142.py`](certificate/check_A056142.py): the 56 data terms; brute force over all
  n < 10^6 (3 digits: palindrome iff n is; 4 to 6 digits: only repdigits); and the word check of steps 1-2 for
  4 <= d <= 400000 (the first mismatch with S(d) occurs within 47 letters).
- Outside Lean: none. Not verified in Lean: agreement of `a` with the OEIS data terms (the script).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry and its history (revisions #3 to #9) contain Wasserman's comment
(3 to 5 digits, no proof given) and the conjecture, unchanged since 2006; no proof is recorded. A web search found
no proof. Not in google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/56142.lean`) or
otoi-lab/oeis-lean-proofs (files A384222, A400194, A8578 only).
