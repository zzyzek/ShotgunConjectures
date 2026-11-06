# OEIS A083942: a(n) = Sum_{k=1..2^n-1} Catalan(k)

**Source.** [A083942](https://oeis.org/A083942) (A. Karttunen): positions of the breadth-first-wise encodings
(A002542) of the complete binary trees (A084107) in A014486. Conjecture (A. Adamchuk, Nov 10 2007, in the entry):
a(n) = Sum_{k=1..2^n-1} A000108(k), equivalently a(n) = A014138(2^n - 2) for n > 0. (OEIS text, checked 2026-11-06.)

**Reading.** [A014486](https://oeis.org/A014486) lists the totally balanced numbers in increasing order, offset 0
(0 = empty word). The breadth-first code of the complete binary tree with s = 2^n - 1 internal nodes lists the s
internal nodes (1) and then the leaves (0), the last leaf dropped: 1^s 0^s = (2^s - 1) 2^s in binary
(A002542: 0, 2, 56, ...). a(n) is the number of totally balanced numbers below it. This reproduces the data
(certificate/check.py).

**Result.** True: a(n) = Sum_{k=1..2^n-1} C_k. More generally, the position of 1^s 0^s in A014486 is
Sum_{k=1..s} C_k for every s.

**Argument.** Totally balanced numbers with 2k binary digits are the Dyck words of semilength k, so there are C_k of
them, and they lie in [2^(2k-1), 2^(2k)). Among words with s ones and 2s digits, 1^s 0^s is the largest. So the words
below 1^s 0^s are 0, all words of semilength 1..s-1, and all but one of semilength s:
1 + C_1 + ... + C_(s-1) + (C_s - 1) = C_1 + ... + C_s.

**Evidence.**
- Lean (Mathlib): [`A083942_mathlib.lean`](A083942_mathlib.lean). `TotBal x` is the A014486 condition on
  `Nat.digits 2 x` read from the most significant bit; `A083942 n` counts `TotBal` numbers below
  `code (2^n - 1)`, `code s = (2^s - 1) * 2^s`. Main theorem `A083942_conjecture : A083942 n = ∑ k ∈ Icc 1 (2^n - 1),
  catalan k`; also `code_balanced` (the code is a term of A014486) and `count_below_code` (all s). Uses Mathlib's
  `DyckWord.card_dyckWord_semilength_eq_catalan`. Checked with `tools/leancheck-mathlib.sh`, no warnings; axioms at
  most propext, Classical.choice, Quot.sound; no sorry, no native_decide.
- [`certificate/check.py`](certificate/check.py): brute-force positions for n <= 3 and the Catalan sums for n <= 7
  equal the data.
- Outside Lean: none. Not verified in Lean: that the breadth-first code of the complete binary tree is 1^s 0^s (a
  one-line reading of the encoding, A002542's formula) and agreement with the data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: A083942 (still "Conjecture"), A014138, A002542, A014486,
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (no entries). No written proof found; the argument
is immediate once the code is recognised as the largest word of its length.
