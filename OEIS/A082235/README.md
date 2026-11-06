# OEIS A082235 / A081847: the triangular numbers 1, 21, 28, 45, 78, 91 are never hit

**Source.** [A081847](https://oeis.org/A081847) (Amarnath Murthy, Apr 10 2003): "a(1) = 1, a(n) = smallest positive
number such that the concatenation of a(n-1) and a(n) is a triangular number not obtained earlier."
[A082235](https://oeis.org/A082235): "Triangular numbers obtained as a concatenation of successive terms of A081847."
Comment in both entries: "Conjecture: Every triangular number other than 3, 6 and 10 is a member."
A081847 also carries a comment by Robert Israel (Dec 30 2018): all terms end in 0, 1, 3, 5, 6 or 8, and
"Triangular numbers that cannot be obtained as concatenation of a(n-1) and a(n) include 1, 3, 6, 10, 21, 28,
45, 78, 91." (OEIS text, CC BY-SA 4.0; A081847 revision #12 of Jan 11 2019, A082235 revision #5 of Nov 30 2025,
checked 2026-11-06.)

**Result.** The conjecture is false: 1, 21, 28, 45, 78 and 91 are triangular and are not members of A082235.

**Argument.** For n ≥ 2, a(n) is the last block of digits of a triangular number, so a(n) mod 10 is a last digit
of a triangular number, one of 0, 1, 3, 5, 6, 8 (m(m+1) mod 20 ∈ {0, 2, 6, 10, 12, 16}); a(1) = 1. A member below
100 is concat(x, y) with x, y > 0, hence a two-digit number 10x + y with y one digit, x = a(n). For 21, 28, 45,
78, 91 this needs x ∈ {2, 4, 7, 9}, which is neither 1 nor a valid last digit. 1 has one digit.

**Evidence.**
- Lean (Mathlib): [`A082235_mathlib.lean`](A082235_mathlib.lean). `A082235_conjecture_false`: for every sequence
  a with a 1 = 1, a (n+1) > 0 and concat (a n) (a (n+1)) triangular for n ≥ 1 (properties the OEIS sequence has
  by definition), concat (a n) (a (n+1)) ∉ {1, 21, 28, 45, 78, 91} for all n ≥ 1. `excluded_are_triangular`.
  `tri_mod10` (last digit of a triangular number). Axioms propext, Classical.choice, Quot.sound; no sorry, no
  native_decide; checked with `tools/leancheck-mathlib.sh`.
- [`certificate/check.py`](certificate/check.py): recomputes A081847 (matches the OEIS data) and lists the triangular
  numbers ≤ 200 not hit in 400 terms: 1, 3, 6, 10, 21, 28, 45, 78, 91.
- Outside Lean: none. Not formalised: that the greedy sequence exists (the theorem holds for every sequence with
  the stated properties, so it is not needed).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Robert Israel's 2018 comment in A081847 states the counterexamples and the
last-digit fact; the conjecture comment was left in both entries. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06).
