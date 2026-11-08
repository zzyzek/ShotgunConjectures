# OEIS A202272: the three conjectured forms are all the terms

**Source.** [A202272](https://oeis.org/A202272): numbers n with k digits such that each sum of 1, 2, ..., k digits
of n is a substring of n (Jaroslav Krizek, 2011). Conjecture in the entry: the terms are exactly the numbers
k·10^j (k, j ≥ 0), the numbers 10X with X a string with one 9 and otherwise zeros (length ≥ 1), and the numbers
9Y10Z with Y, Z strings of zeros (possibly empty). (OEIS text, CC BY-SA 4.0, cached entry, checked 2026-11-07.)

**Reading.** "Sum of i digits" is the sum over any i digit positions (example in the entry: 109 needs 0, 1, 9, 10).
A sum is "a substring" if its decimal representation occurs as a contiguous block of digits of n.

**Result.** The conjecture is true.

**Argument.** Let M be the multiset of nonzero digits of n, m = |M|, S = ΣM. Every sum over a nonempty
sub-multiset of M must occur in n (zero digits change nothing: sum 0 occurs iff n has a 0). If m ≤ 1, n = k·10^j
and n is a term. Let m ≥ 2. For a value v with ℓ digits and leading digit c, an occurrence starts at a position
holding c; distinct values of the same length need distinct starting positions.

1. S ≥ 10: otherwise S is one digit, so S ∈ M, but S exceeds every element of M (m ≥ 2).
2. 1 ∈ M: add the digits one at a time; partial sums rise by at most 9 from 0 to S ≥ 10, so some partial sum lies
   in [10, 18] and its first digit 1 occurs in n.
3. If M has two 1s: 1+1 = 2 occurs, so 2 ∈ M; then 1+2 = 3 ∈ M, ..., 1+8 = 9 ∈ M. Now {1..9} ⊆ M, and every
   v ∈ [1, S] is a sub-multiset sum (adding elements in increasing order, each is at most 1 + the sum before it).
   Count positions: S ≥ 45 needs 10..45, so c_1, c_2, c_3 ≥ 10, c_4 ≥ 6, c_5..c_9 ≥ 1 (c_d = copies of d in M),
   giving S ≥ 119. If S ≥ 10^(L-1) with L ≥ 3: all (L-1)-digit values occur, c_d ≥ 10^(L-2) for every d, so
   S ≥ 45·10^(L-2); then all L-digit values below 4.5·10^(L-1) occur, c_1, c_2, c_3 ≥ 10^(L-1), so
   S ≥ 6·10^(L-1) + 39·10^(L-2) = 9.9·10^(L-1); then c_1..c_8 ≥ 10^(L-1) and S ≥ 36·10^(L-1) ≥ 10^L. By induction S
   exceeds every power of 10, impossible.
4. So M has exactly one 1. Let d be the least other element. If d ≤ 8: 1+d, 1+(d+1), ... occur, so d, ..., 9 ∈ M;
   8+9 = 17 puts 7 in M; 7+8 = 15 puts 5 in M; 5+6 = 11 needs two 1s, contradiction. So d = 9, and two 9s would
   give 18, putting 8 in M. Hence M = {1, 9}.
5. M = {1, 9}: the sums are 1, 9, 10, so n is a term iff "10" occurs, i.e. the 1 is followed by a 0. Leading 1
   gives 10X; leading 9 gives 9Y10Z. Both forms are terms.

**Evidence.**
- [`certificate/check_A202272.py`](certificate/check_A202272.py): all n < 10^7 by the definition; the 94 terms
  are exactly the three forms (no mismatch).
- Lean (Mathlib): [`A202272_mathlib.lean`](A202272_mathlib.lean). `IsTerm n`: for every nonempty sublist of
  the digit list of n, the digit list of its sum is an infix of the digit list of n. Main theorem
  `A202272_main : IsTerm n ↔ (NZ n).length ≤ 1 ∨ ((NZ n).Perm [1, 9] ∧ [0, 1] <:+: D n)` (NZ = nonzero
  digits). Steps 1-5 are `sum_ge_ten`, `one_mem_digits`, `no_two_ones` (with `cover`, `card_infSet`,
  `block_count`), `no_mid`, `no_two_nines`, `forward`, `backward`. Check: `tools/leancheck-mathlib.sh`, no
  warnings, axioms propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`.
- Outside Lean: none. Not verified in Lean: the one-line translation of the characterization into the three
  written forms (leading digit 1 gives 10X, leading digit 9 gives 9Y10Z).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: the OEIS entry (still a conjecture), google-deepmind/formal-conjectures,
otoi-lab/oeis-lean-proofs: nothing found.
