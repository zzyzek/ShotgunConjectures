# OEIS A094044: 4 is never a term, so 5 is not the only nonmember

**Source.** OEIS [A094044](https://oeis.org/A094044): alternately prime and nonprime numbers, not used
earlier, such that every concatenation of a pair of consecutive terms is prime; a(1) = 2. Old comment
(R. G. Wilson v, 2004): "Conjecture: 5 is the only nonmember." Removed by Robert Israel on
2017-10-24, who noted in the edit discussion that all terms except 2 are odd and none ends in 5, and
replaced it by "all members of A045572 are in the sequence".

**Result.** False: for n ≥ 2 every a(n) is odd and not divisible by 5, so 4, 6, 15, … never occur.

**Argument.** For n ≥ 2 the concatenation a(n−1)·10^L + a(n) (L ≥ 1 digits) is ≥ 10 and ≡ a(n) mod 10.
If 2 or 5 divided a(n) it would divide this prime, which exceeds 5.

**Evidence.** Lean (Mathlib): [`A094044_mathlib.lean`](A094044_mathlib.lean), `A094044_odd_not5`,
`A094044_main` (a(n) ≠ 4), for every sequence of positive integers with a(1) = 2 whose consecutive
decimal concatenations are prime. Axioms propext, Classical.choice, Quot.sound. Outside Lean: that
A094044 has these properties (its definition; the greedy choice is not used).

**Review level.** `lean-proof`.

**Prior art.** Known: R. Israel, A094044 edit discussion, 2017-10-24. Not in formal-conjectures or
oeis-lean-proofs (2026-11-07). The replacement conjecture (A045572 ⊂ A094044) is open and not
treated here.
