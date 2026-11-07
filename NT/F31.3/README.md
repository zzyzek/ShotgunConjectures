# Guy UPINT F31: which integers are quotients of integers with ternary digits 0, 1?

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section F31 (paraphrased): after Selfridge and
Lacampagne's question for digits ±1 in base 3 (answered negatively by Coppersmith, k = 247), Guy asks which integers
can be written as a / b with a, b having base-3 digits 0 and 1 only.

**Reading.** k ≥ 1, a, b ≥ 1. Since k is a quotient iff 3k is (append or strip a final 0 digit), it suffices to
treat 3 ∤ k.

**Result.** Partial; all three statements are known (OEIS A339636, J. Shallit 2020; Anders, Dawsey, Reznick,
Sisneros-Thiry, arXiv:2308.07252). For 3 ∤ k:
1. k ≡ 2 (mod 3) is never a quotient (the last nonzero digit of k·b would be 2).
2. No k with 1.5·3^m < k < 2·3^m (some m) is a quotient.
3. Computation: every other k ≡ 1 (mod 3) below 10^5 is a quotient except the six sporadic values
   529, 592, 601, 616, 5368, 50281 (exactly the first six terms of OEIS A339636, which continues 4072741, ...).
So below 10^5 the non-quotients are exactly the k ≡ 2 (mod 3) family, the intervals (1.5·3^m, 2·3^m) (times powers
of 3), and six sporadic values. A339636 has 22 sporadic terms below 3.5·10^8 and conjectures that 23·3^(4k+3) - 20 is
never representable; a rule for the sporadic set (and its infinitude) remains open.

**Argument.** (2): if a has ℓ ternary digits, all 0 or 1, then 3^(ℓ-1) ≤ a and 2a < 3^ℓ. With a = k·b, ℓ_a and
ℓ_b the digit counts, 3·3^m < 2k gives 3^(m+ℓ_b) < 3^(ℓ_a), and k < 2·3^m gives 3^(ℓ_a) < 3^(m+ℓ_b+1): no integer
ℓ_a fits. This is the integer form of the description of quotients of the Cantor set (Athreya-Reznick-Tyson 2019). (3): k is a quotient iff the long multiplication k·b, with b's digits chosen in {0,1}
from the right, reaches a carry whose own digits are 0/1 without ever writing a digit 2; carries stay below k, so a
breadth-first search over (carry, b ≠ 0) decides each k.

**Evidence.**
- Lean (Mathlib): [`F31_3_mathlib.lean`](F31_3_mathlib.lean), namespace `NT_F31_3`, with `IsQuot k` defined from
  `Nat.digits 3`. Main theorems `interval_obstruction` (statement 2) and `not_quotient_of_mod3` (statement 1).
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/f313.c`](certificate/f313.c) (k ≤ 10^5, output `sporadic_1e5.txt`) and
  [`certificate/f313.py`](certificate/f313.py) (k < 20000, the same answer).
- Outside Lean: statement 3 (the search and its correctness), the sporadic exceptions themselves.

**Review level.** `lean-proof` for statements 1 and 2; `agent` for the search.

**Prior art.** Checked 2026-11-06: OEIS A339636/A339637 (Shallit; the interval obstruction is stated there as easy,
the sporadic terms listed) and Anders-Dawsey-Reznick-Sisneros-Thiry, arXiv:2308.07252 (2023: a necessary and almost
sufficient condition, a decision algorithm, complete description to 364). Athreya-Reznick-Tyson, Cantor set
arithmetic, Amer. Math. Monthly 126 (2019). OEIS A068196 (cited by Guy) is unrelated. Not in
google-deepmind/formal-conjectures (clone 2026-11-06).
