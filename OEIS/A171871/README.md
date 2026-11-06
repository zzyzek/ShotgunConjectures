# OEIS A171871: the last 2^(R-1) entries of column R are binary-code counts (A039754)

**Source.** [A171871](https://oeis.org/A171871) (Robert Munafo, 2010), "Triangle read by rows: Distinct
classifications of N elements containing exactly R binary partitions." Comment: "Conjecture: In general, in
each column, the last 2^(R-1) values are the same as the first 2^(N-1) values from the corresponding row of
A039754. - Robert Munafo, Dec 30 2009". [A005646](https://oeis.org/A005646) defines a classification: a set of
type-specimens each separated from the others by a set of binary partitions, none of which can be omitted
without leaving two types unseparated. [A039754](https://oeis.org/A039754): T(R, N) = number of binary codes of
length R with N words (up to coordinate permutations and complementations). (OEIS text, CC BY-SA 4.0, checked
2026-11-06.)

**Reading.** "2^(N-1)" in the comment means 2^(R-1) (row R of A039754 has 2^R + 1 entries). Encode a
classification by listing its R partitions, choosing a side of each, and writing each element's 0/1 word: the
result is a set C of N distinct words in {0,1}^R whose columns are nonconstant, pairwise neither equal nor
complementary, and such that deleting any column makes two words equal. Isomorphism of classifications is the
action of the hypercube group (coordinate permutations and flips) on C. This reading reproduces A171871 for
R ≤ 4 and all N (`certificate/check.py`). Column R of A171871 is nonzero for R < N ≤ 2^R, so its last 2^(R-1)
entries are N = 2^(R-1)+1, ..., 2^R.

**Result.** True: A(N, R) = T(R, N) for 2^(R-1) < N, and T(R, N) = T(R, 2^R − N), so the last 2^(R-1) values of
column R are T(R, 2^(R-1)+1..2^R) = the first 2^(R-1) values of row R of A039754 read backwards.

**Argument.** Let C have N > 2^(R-1) words. If deleting coordinate i were injective on C, then
N ≤ 2^(R-1). So deleting any coordinate merges two words (minimality); a constant column i, or a column j equal
or complementary to column i, would make deleting i (resp. j) injective, so neither occurs. Hence every N-word
code is a classification, and the two counts are the same orbit count. Complementing C (w ↦ every word not in
C) commutes with the group and maps N-word codes to (2^R − N)-word codes, giving T(R, N) = T(R, 2^R − N).

**Evidence.**
- Lean (Mathlib): [`A171871_mathlib.lean`](A171871_mathlib.lean). `T R N` and `A N R` are numbers of classes
  (`Nat.card` of a quotient) of N-word codes of length R, all or classifications, under the hypercube group.
  Theorems: `isClassification_of_card`, `A_eq_T` (2^(R-1) < N → A N R = T R N), `T_compl`, and
  `A171871_conjecture` (R ≥ 1, 1 ≤ k ≤ 2^(R-1): A(2^(R-1)+k, R) = T(R, 2^(R-1)+k) = T(R, 2^(R-1)−k)).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): brute-force orbit counts for R ≤ 4 match A171871 and A039754.
- Outside Lean: the encoding of a classification of N unlabeled elements by a set of partitions as a code up to
  the hypercube group (definition reading only); agreement with the OEIS data (check.py, R ≤ 4).

**Review level.** `lean-proof` (for the code reading of the definition).

**Prior art.** Checked 2026-11-06. A039754 carries the comment "For N=1 through N=5, the first 2^(N-1) terms of
row N are also found in triangle A171871 ... This was shown for all N by Andrew Weimholt, Dec 30 2009" (Munafo,
Jan 25 2010); no proof is written in the entries. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06). The argument above is ours; it is immediate.
