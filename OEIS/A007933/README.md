# OEIS A007933 (also A007934, A007935): a(n) ~ 3n/2 — partial result

**Source.** [A007933](https://oeis.org/A007933) "Some permutation of digits is a prime" (R. Muller);
[A007934](https://oeis.org/A007934) "Some nontrivial permutation of digits is a prime";
[A007935](https://oeis.org/A007935) "Composite numbers such that some permutation of digits is a prime".
Each entry carries the comment "Conjecture: a(n) ~ 3n/2" (C. R. Greathouse IV, Sep 19 2012).
OEIS text, CC BY-SA 4.0, checked 2026-11-07.

**Reading.** Leading zeros are allowed in the permutation: 20, 30, 50, 70 are terms (02 = 2 etc.). The data
of A007933 is reproduced up to 10^5 by brute force under this reading (certificate/brute.py: 4, 41, 457, 5458,
60774 terms below 10^1, ..., 10^5). a(n) ~ 3n/2 is equivalent to: the set has natural density 2/3.

**Result (partial).**
1. *The three conjectures are equivalent.* A007935 is A007933 minus the primes. A term of A007933 that is not
   in A007934 has the identity as its only prime arrangement, so it is prime. Both differences lie in the primes,
   a set of density 0, so the three sets have the same upper and lower densities.
2. *Upper half.* Every arrangement of the digits of n is congruent to n mod 3, so a term divisible by 3 has an
   arrangement equal to 3, i.e. its digits are one 3 and zeros (n = 3·10^j). Hence
   #{terms <= x} <= ⌈2x/3⌉ + log10(x) + 1, and liminf a(n)/n >= 3/2.
3. *Remaining statement.* The conjecture is equivalent to: almost all n coprime to 3 (in natural density) have
   a prime digit arrangement. Numbers whose digits avoid {1, 3, 7, 9} have density 0 (at most (6/10)^k of the
   k-digit numbers), so it is also equivalent to: almost all n coprime to 3 that contain one of the digits
   1, 3, 7, 9 have a prime arrangement.
4. *Computation.* Exact count of terms below 10^k for k <= 18 by enumerating digit multisets
   (certificate/classes.c; deterministic Miller-Rabin for 64-bit integers; random arrangements first, then
   exhaustive enumeration of the class when 400 random tries fail). Proportion of terms among the numbers
   below 10^k that are coprime to 3: 0.9514 (k = 6), 0.98315 (k = 8), 0.993952 (k = 10), 0.997823 (k = 12),
   0.999216 (k = 14), 0.999718 (k = 16), 0.999831 (k = 17), 0.999898 (k = 18); count below 10^18:
   666 598 960 028 305 743 (outputs: certificate/classes.out, certificate/classes2.out).
   The missing mass is almost entirely the digit sets with no digit 1, 3, 7, 9; the remaining failing classes
   (certificate/classes2.c) are classes in which one digit fills all but at most two places (for example
   1111111111, or nine 4s and one 1), about 10^4 numbers per decade for k = 10..14.

**Argument.** Items 1 and 3 are as written. Item 2: 10 ≡ 1 mod 3, so an arrangement l of the digits reads as a
number ≡ (sum of l) = (digit sum of n) ≡ n mod 3; a prime divisible by 3 is 3; and an arrangement equal to 3 has
exactly one nonzero digit, a 3.

**Evidence.**
- Lean (Mathlib): [`A007933_mathlib.lean`](A007933_mathlib.lean). `A007933IsTerm n` = some permutation of
  `Nat.digits 10 n` read by `Nat.ofDigits 10` is prime. `A007933_mod_three_perm` (any arrangement ≡ n mod 3),
  `A007933_three_dvd` (3 ∣ n and n a term ⇒ some arrangement equals 3). Checked with
  `tools/leancheck-mathlib.sh`: OK, axioms at most propext, Classical.choice, Quot.sound.
- Outside Lean: the counting bound in item 2 (numbers ≤ x with digits {3, 0, ..., 0}), the equivalences in
  items 1 and 3, and the computation in item 4.

**Obstruction.** The lower bound needs, for almost every digit multiset (weighted by the number of its
arrangements), a prime among its arrangements: a mean-square local limit theorem for the 10-dimensional digit
count vector of primes. Drmota-Mauduit-Rivat (2009) proved the one-dimensional local theorem (primes with a
given digit sum); the multidimensional version is not available. Details in the scan's
work/OEIS-A007933/REPORT.md.

**Review level.** `lean-proof` for item 2's arithmetic core; `rechecked` for the computation.

**Prior art.** Checked 2026-11-07: the three OEIS entries (conjecture still stated), web search for density
of numbers with a prime digit permutation (nothing found), google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs (no entry).
