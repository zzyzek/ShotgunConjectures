# OEIS A023402 / A081532: T(n,3) and A023402 differ at n = 4

**Source.** OEIS wiki Talk:Conjectures/List. For [A023402](https://oeis.org/A023402) (line 102):
"Conjecture: a(n) = 3rd divisor of smallest number having exactly n+2 divisors, a(n)=T(n+2,3), T as defined
in A081532." For [A081532](https://oeis.org/A081532) (line 406): "Conjecture: T(n,3) = A023402(n-2) for n>2."
(OEIS text, CC BY-SA 4.0.) Neither comment is in the current entries (checked 2026-11-01).

**Result.** Both false: A023402(2) = 4 but T(4,3) = 3.

**Argument.** The smallest number with 4 divisors is 6, with divisors 1, 2, 3, 6, so T(4,3) = 3.
A023402 lists, right to left, the last digits of a power of 2 whose last k digits are all 3 or 4. The
two-digit endings drawn from {3, 4} are 33, 34, 43, 44; 33 and 43 are odd, and 34 ≡ 2 (mod 4) while
4 | 2^e for e ≥ 2; 2^18 = 262144 ends in 44. So A023402(1) = A023402(2) = 4. (The two sequences do agree
at n = 3: A023402(1) = 4 = T(3,3).)

**Evidence.**
- Lean (Mathlib): [`A023402_mathlib.lean`](A023402_mathlib.lean) proves `A023402_main`: some 2^e has its last two digits in {3, 4} and every such 2^e ends in 44 (so A023402(2) = 4 under the reading "A023402(k) = k-th last digit of a power of 2 whose last k digits are 3s and 4s", stated in the file header); 6 is the least number with 4 divisors (Mathlib `IsLeast`, `Nat.divisors`), its divisors are {1, 2, 3, 6}, so T(4, 3) = 3. Outside Lean: nothing beyond that reading of the definition.
- Lean: [`A023402.lean`](A023402.lean) and [`../A081532/A081532.lean`](../A081532/A081532.lean) (same content):
  divisor counts of 1..6, divisors of 6, 2^e ≡ 0 (mod 4) for e ≥ 2, 2^18 ≡ 44 (mod 100). Nothing outside
  Lean except the reading of the A023402 definition.
- `certificate/check.py`: T(n,3) for n ≤ 12 and the two-digit endings.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`A023402_mathlib.lean`](A023402_mathlib.lean)) under the reading of the A023402 definition stated in its header.
**Prior art.** Known. J. Lowell noted in 2020 that the conjecture is wrong (the T(n,3) column is [A171783](https://oeis.org/A171783)), and the comment was then removed ([history](https://oeis.org/history?seq=A023402)). Searched OEIS entries, references and history. Checked 2026-11-04.
