# OEIS A083125: palindromic multiples of 81 have digit sum divisible by 81, so 81 enters very late

**Source.** OEIS [A083125](https://oeis.org/A083125): a(1) = 1, then the smallest number not
occurring earlier such that the product of a pair of successive terms is a palindrome.
Conjecture (R. Zumkeller, May 02 2003): "except for multiples of 10, all natural numbers belong
to this sequence" (OEIS text, CC BY-SA 4.0).

**Result (partial; the conjecture stays open).**
1. (Lean) If P is a decimal palindrome and 81 ∣ P, then 81 divides the digit sum of P, and
   P ≥ 10^8. Precisely 2P ≡ S·(9n − 7) (mod 81) with S the digit sum and n the number of digits.
   For even n the digit sum is even, so 162 ∣ S; hence no palindrome with 2–10 digits except
   999999999 is divisible by 81.
2. Consequence for the sequence. Every number below 81 that is not a multiple of 10 occurs
   (they all occur among the first 2000 terms), so 81 is a term exactly when some term a satisfies
   81·a palindromic, and then 81 comes right after the first such a. By part 1 this needs
   a = 12345679 (81a = 999999999) or a ≥ 123456791 (81a has at least 11 digits).
   The same mechanism delays every multiple of 81.
3. (Computation) After 180000 terms the least missing non-multiple of 10 is still 81
   (`certificate/seq200000.out`, run stopped by its time limit at k = 180000+); after 60000 terms the missing ones below 2000 are the 22
   multiples of 81 below 2000 that are not multiples of 10, and 1465.
   The largest of the first 60000 terms is 119094117, just below 123456791; 12345679 has not
   occurred among them. All non-multiples of 10 below 81 occur among the first 2000 terms.

**Argument.** 10^i = (1 + 9)^i ≡ 1 + 9i (mod 81), so P = Σ d_i 10^i ≡ S + 9W with W = Σ i d_i.
For a palindrome the reversal i ↦ n − 1 − i fixes the digit string, so 2W = (n − 1)S and
2P ≡ 2S + 9(n − 1)S = S(9n − 7). Since 3 ∤ 9n − 7, 81 ∣ P forces 81 ∣ S, and S ≤ 9n
forces n ≥ 9, P ≥ 10^8.

**Evidence.**
- Lean (Mathlib): [`A083125_mathlib.lean`](A083125_mathlib.lean). `A083125_mod81`
  (ofDigits ≡ S + 9W mod 81), `A083125_W_reverse`, `A083125_pal81` (palindrome, 81 ∣ P ⇒ 81 ∣ S),
  `A083125_pal81_large` (P ≥ 10^8). Palindrome means `(Nat.digits 10 P).reverse = Nat.digits 10 P`.
  Axioms propext, Classical.choice, Quot.sound; zero warnings.
  Outside Lean: part 2 (two lines from the definition and the first 2000 terms) and the computations.
- `certificate/seq.c`, `certificate/seq2.c`: generator (ascending palindromes, bitmap of used values);
  reproduces the listed terms.

**Review level.** `lean-proof` for the lemma; `rechecked` for the computation.

**Prior art.** OEIS A083125 (checked 2026-11-07, b-file to n = 2000 by J.-M. Falcoz) states the
conjecture only. The congruence 10^i ≡ 1 + 9i (mod 81) is elementary and classical; its use for
palindromes is not stated in the entry. Palindromes in residue classes modulo q with
gcd(q, 990) > 1 are excluded from Col's equidistribution theorem (Acta Arith. 137 (2009)), which
matches the bias found here. google-deepmind/formal-conjectures, otoi-lab/oeis-lean-proofs: no entry.
