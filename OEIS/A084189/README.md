# OEIS A084189: the minimum digit of the factors is never greater than 3

**Source.** [A084189](https://oeis.org/A084189) (Jason Earls, Jun 20 2003): minimum digit of the two prime factors of
the terms of [A046376](https://oeis.org/A046376), the palindromes p q with p, q palindromic primes. "Conjecture: a(n)
is never greater than 3." Suggested by an old JRM problem: find a composite palindrome larger than 343 whose prime
factors are palindromes with all digits greater than 3. (OEIS text, CC BY-SA 4.0, checked 2026-11-07.)

**Result.** True, and sharper: a(n) = 3 only for the term 9 = 3 * 3 (n = 3); a(n) <= 2 for every other n.

**Argument.** Let p, q be primes whose digits are all >= 3, with a and b digits, and (p, q) != (3, 3).
1. *Length.* A number with a digits all >= 3 is at least 33...3 = (10^a - 1)/3. If a, b >= 2 this gives
   pq >= (10^a - 1)(10^b - 1)/9 >= 10^(a+b-1). If a = 1 then p is 3, 5 or 7; for p >= 5,
   pq >= 5(10^b - 1)/3 >= 10^b; for p = 3, 3q >= 10^b - 1 with equality only if q = 33...3, which is divisible by 3,
   so q = 3, excluded. Hence pq has exactly a + b digits.
2. *Odd lengths.* An even-length palindrome is divisible by 11 (alternating digit sum 0). A palindromic prime with
   all digits >= 3 is not 11, so a and b are odd.
3. Then pq has a + b digits, an even number; if pq were a palindrome, 11 | pq, so p = 11 or q = 11. Impossible.
So every term p q of A046376 other than 9 has a factor with a digit <= 2; for 9 the minimum digit is 3.

**Evidence.**
- Lean (Mathlib): [`A084189_mathlib.lean`](A084189_mathlib.lean). Main theorems `A084189.A084189_main` (digits >= 4:
  for palindromic primes p, q with all digits >= 4, p * q is not a palindrome) and `A084189.A084189_sharp`
  (digits >= 3: p * q palindrome forces p = q = 3). The same file proves A084352 (`A084352_main`,
  `A084352_sharp`). Mathlib's `Nat.eleven_dvd_of_palindrome` gives step 2. Check: `tools/leancheck-mathlib.sh`,
  exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- Outside Lean: none. The Lean statements quantify over all prime pairs; reading A046376 as "palindromes p q with
  p, q palindromic primes" is the entry's definition.
- [`certificate/jrm_search.py`](certificate/jrm_search.py): the JRM question itself (any number of prime factors,
  with multiplicity, all palindromic with digits >= 4) up to 10^13: the only composite palindrome is 343 = 7^3.
- [`certificate/nonpal_factor_search.c`](certificate/nonpal_factor_search.c): without the palindromic-factor
  condition the statement fails (38983 = 7 * 5569); the palindromic factors are what makes step 2 work.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: OEIS A084189, A046376 (comments by F. T. Adams-Watters 2011 and M. F. Hasler 2022
discuss trivial families, no proof of the conjecture), web search, google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs local clones (2026-11-06): nothing found. The 11-divisibility of even-length palindromes
is classical, so the proof is immediate once the length count (step 1) is noticed. The JRM question for composites
with three or more factors stays open (searched to 10^13).
