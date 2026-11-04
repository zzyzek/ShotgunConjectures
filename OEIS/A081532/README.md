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
- Lean: [`../A023402/A023402.lean`](../A023402/A023402.lean) and [`A081532.lean`](A081532.lean) (same content):
  divisor counts of 1..6, divisors of 6, 2^e ≡ 0 (mod 4) for e ≥ 2, 2^18 ≡ 44 (mod 100). Nothing outside
  Lean except the reading of the A023402 definition.
- `certificate/check.py`: T(n,3) for n ≤ 12 and the two-digit endings.
- Lean (Mathlib): [`A081532_mathlib.lean`](A081532_mathlib.lean), `A081532_main`: T(4,3) = 3 with T defined from the A081532 definition (k-th smallest divisor of the least number with n divisors), and every sequence with the defining property of A023402 (its OEIS name: the last k digits of a power of 2 drawn from {3,4} are its first k terms reversed) has a(2) = 4. So the reading of A023402 is formalised; nothing else outside Lean.

**Review level.** `lean-proof` (Mathlib file above; A023402 read by its OEIS name).
**Prior art.** Known. J. Lowell noted in 2020 that the conjecture is wrong (column 3 of A081532 is [A171783](https://oeis.org/A171783)), and the comment was removed from both entries ([history](https://oeis.org/history?seq=A023402)). Searched OEIS entries, references and history. Checked 2026-11-04.
