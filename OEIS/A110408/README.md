# OEIS A110408: zeros are not only palindromic primes and multiples of 3

**Source.** [A110408](https://oeis.org/A110408): smallest prime which is the repeated reverse concatenation of n
followed by n (ending in n), n ≡ 1, 3, 7, 9 (mod 10), or 0 if no such prime exists. Conjecture (entry):
"a(n) is 0 iff n is a palindromic prime == 1,3,7 or 9 (mod 10) and/or n ==0 (mod 3)." (scan list; entry
data and wording as cached 2026-11-07).

**Reading.** The candidates are N_k(n) = rev(n) rev(n) ... rev(n) n with k >= 1 copies of rev(n), e.g.
a(17) = 71717117 = N_3(17), a(1) = 11 = N_1(1).

**Result.** The "if" direction holds; the "only if" direction is false, for two independent reasons.
1. Every palindrome n > 1 (prime or not) has a(n) = 0: then N_k is n written k+1 times, a proper multiple of n.
   So a(121) = 0 (121 = 11^2, 3 ∤ 121), also 161, 323, 343, 707, ...
2. Covering congruences give zeros at non-palindromes: for a 3-digit n, 10^3 ≡ -1 (mod 1001) gives
   N_k ≡ n (mod 1001) for k even and N_k ≡ n - rev(n) (mod 1001) for k odd, and n - rev(n) is a multiple of 99.
   So if 7 | n or 13 | n (or 11 | n), every N_k has the factor 7, 13 or 11 (k even) or 11 (k odd). Example:
   n = 119 = 7·17, rev = 911: 7 | N_k for even k, 11 | N_k for odd k, so a(119) = 0, though 119 is not a
   palindrome and 3 ∤ 119.
The "if" direction: 3 | n gives 3 | N_k (digit sums), and palindromic primes are case 1.

**Evidence.**
- Lean (core): [`A110408.lean`](A110408.lean): `palin_composite` (rev n = n, n > 1 → n | N_k and n < N_k),
  `A110408_121`, `A110408_121_zero`; `rep3_mod` and `A110408_119` (7 or 11 divides N_k(119), N_k > 11, every
  k >= 1), `A110408_119_facts` (rev 119 = 911, 3 ∤ 119, not a palindrome); `three_composite` (the "if" part
  for 3 | n, given rev n ≡ n mod 3). Checked with `tools/leancheck.sh`; axioms at most propext,
  Classical.choice, Quot.sound.
- [`certificate/search.gp`](certificate/search.gp), [`search.out`](certificate/search.out): for the 497
  non-palindromic n <= 2000 with n ≡ 1,3,7,9 (mod 10) and 3 ∤ n, those with no probable prime N_k, k <= 400.
- [`certificate/covering.py`](certificate/covering.py), [`covering.out`](certificate/covering.out): 71 of
  them have a covering set of primes < 2000 with period dividing 720 (all of the 3-digit ones divisible by
  7, 11 or 13, and others such as 1169, 1207, 1253, 1369).
- Outside Lean: none for the counterexamples. Not verified in Lean: that rev n ≡ n (mod 3) in general.

**Open remainder.** Which non-palindromic n with 3 ∤ n have a(n) = 0. Some (e.g. 53, 103, 107, 113, 157)
have no probable prime N_k for k <= 400 and no covering found with period 720 or 5040; deciding them is a
Sierpiński-type problem for the family N_k.

**Review level.** `lean-witness`.

**Prior art.** OEIS A110408 (conjecture as stated, no correction), google-deepmind/formal-conjectures (no file),
otoi-lab/oeis-lean-proofs (none); 2026-11-07.
