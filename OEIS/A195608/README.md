# OEIS A195608: first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts

**Source.** [A195608](https://oeis.org/A195608): "Numbers n such that Sum_{i=1..n} A(i) = A(n)*A(n+1)/4, where
A(n) = A001969(n)" (evil numbers, offset 1, A(1) = 0). Comment by V. Shevelev (2011): "Conjectures: 1) there are
only 3 different first differences 1,4,6; 2) the sequence contains either isolated series of terms, e.g.,
{1},{7},{25},{31},..., or series of 3 consecutive integers, e.g., {11,12,13}, {19,20,21}, etc.; 3)the first terms m
of every series satisfy the condition A(m+1)-A(m-1)=5, where A(n)=A001969(n)." (OEIS text, CC BY-SA 4.0; entry
fetched 2026-11-05, unchanged since Dec 2019.) The twin entry for odious numbers is [A195609](../A195609/README.md).

**Reading.** S = {n ≥ 1 : 4·Σ_{i≤n} A(i) = A(n)A(n+1)} (the same as the /4 equation). A "series" is a maximal
run of consecutive integers in S; the comment's examples count the singletons {1}, {7} as series.
- 1) For every n ∈ S the next element of S is n + 1, n + 4 or n + 6 (this also gives that S is infinite);
  all three differences occur.
- 2) If [a, b] ⊆ S, a − 1 ∉ S and b + 1 ∉ S, then b = a or b = a + 2.
- 3) If m ∈ S and m − 1 ∉ S then A(m+1) − A(m−1) = 5, for m ≥ 2. The series {1} has m = 1 and A(0) does not
  exist, so m = 1 is excluded (it is the only run start below 2). Read with singletons included, as the comment's
  wording does; for runs of 3 alone the statement is a special case.

**Result.** All three conjectures are true. Closed form, with t the Thue–Morse sequence (A010060):
S = {2j+1 : t(j) = 0} ∪ {2j+2 : t(j) = t(j+1) = 0}. Sharper form of 3): for m ∈ S, m ≥ 2,
A(m+1) − A(m−1) is 5 if m starts its series and 4 otherwise.

**Argument.** A(k+1) = 2k + t(k) (A001969 comment, Alekseyev), t(2j) = t(j), t(2j+1) = 1 − t(j), so
Σ_{k<2j} t(k) = j and Σ_{i≤n} A(i) = n(n−1) + Σ_{k<n} t(k). Write a = t(j), b = t(j+1).
- n = 2j+1: the equation is 16j² + 12j + 4a = (4j + a)(4j + 3 − a), true iff a = 0.
- n = 2j+2: it is 16j² + 28j + 12 = (4j + 3 − a)(4j + 4 + b), true iff a = b = 0.
Let Z = {j : t(j) = 0}. t never takes one value three times in a row (t(2i) ≠ t(2i+1)).
- 1) n = 2j+2 ∈ S gives 2j+3 ∈ S. For n = 2j+1, j ∈ Z, the next zero of t after j is j+1, j+2 or j+3, giving the
  next element 2j+2, 2j+5 or 2j+7; the even numbers in between need two consecutive zeros, which are absent.
- 2) Every even element 2j+2 brings 2j+1 and 2j+3 with it, and 2j, 2j+4 ∉ S (each would need three zeros of t
  in a row). A run of length ≥ 2 contains an even element, so it is exactly {2j+1, 2j+2, 2j+3}.
- 3) Series start m = 2j+1 with j ∈ Z, j ≥ 1, t(j−1) = 1. A(m+1) − A(m−1) = 4 + t(2j+1) − t(2j−1)
  = 4 + t(j−1) − t(j) = 5.

**Evidence.**
- `certificate/check.py`: computes S directly for n ≤ 400000 for both entries, compares with the closed form and
  the OEIS b-files (10000 terms each, all equal), and checks 1)–3) and the sharper form there.
- Lean (Mathlib): [`A195608_mathlib.lean`](A195608_mathlib.lean) (shared with A195609). Definitions:
  `tm n = (Nat.digits 2 n).sum % 2`, `evil n = Nat.nth (fun k => tm k = 0) (n - 1)`,
  `A195608set = {n | 1 ≤ n ∧ 4 * ∑ i ∈ Icc 1 n, evil i = evil n * evil (n + 1)}`; `evil_values` and
  `A195608_values` check the first 20 evil numbers and S ∩ [0, 50) against OEIS by `decide`. Theorems:
  `A195608_closed_form`; `A195608_conj1` (∃ d ∈ {1, 4, 6}, n + d ∈ S and no k ∈ S with n < k < n + d);
  `A195608_conj1_occur` (1 → 7, 7 → 11, 11 → 12); `A195608_conj2` (b = a ∨ b = a + 2);
  `A195608_conj3` (m ∈ S, 2 ≤ m, m − 1 ∉ S → evil (m+1) − evil (m−1) = 5); `A195608_conj3_iff`. Axioms:
  propext, Classical.choice, Quot.sound. Nothing outside Lean.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: OEIS entries A195608, A195609 (still "Conjectures", no proof), A001969 (has
A(n) = 2(n−1) + t(n−1) with proof, the only ingredient used); web search for the A-numbers with "proof"/"Lean";
Shallit, "Using Walnut to solve problems from the OEIS" (arXiv:2503.04122) and Adamczewski, "OEIS Open"
(arXiv:2608.11941): neither mentions A195608/A195609; google-deepmind/formal-conjectures has no entry (checked
earlier). No proof found; the closed form and proof here are new as far as found.
