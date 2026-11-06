# OEIS A113676: row lengths of Golomb's sequence cut into rows = first differences of A014644

**Source.** [A113676](https://oeis.org/A113676) (Floor van Lamoen and Paul D. Hanna, Nov 06 2005): take Golomb's
sequence [A001462](https://oeis.org/A001462) with one fewer 2 (1, 2, 3, 3, 4, 4, 4, 5, ...) and cut it into rows: row 1
is [1], row n has as many elements as the row sum of row n-1; a(n) = number of elements of row n (1, 1, 2, 6, 27,
234, ...). Comments: "Conjecture: a(n) for n>1 gives first differences of Lionel Levine's sequence A014644(n) for
n>=3." and "Conjecture: Final elements of the rows form A014644 except for duplicate 2."
[A014644](https://oeis.org/A014644): array starting with {1,1}, the i-th term of a row gives the number of i's in the
next row; final term of each row. (OEIS text, CC BY-SA 4.0, A113676 revision #9 of Mar 05 2025, checked 2026-11-06.)

**Reading.** Conjecture 1: a(n) = A014644(n+2) - A014644(n+1) for n ≥ 2 (n = 2: 3 - 2 = 1). Conjecture 2: row 1 ends
in A014644(1) = 1 and row n ≥ 2 ends in A014644(n+1), so the final elements are A014644 with one of its two 2s removed.

**Result.** Both conjectures are true.

**Argument.** Let Γ map a list (c_1, ..., c_m) to c_1 copies of 1, then c_2 copies of 2, and so on; A014644's rows
are R_1 = (1,1), R_{k+1} = Γ R_k, and A014644(n) is the last term of R_n.
1. Golomb's sequence G is nondecreasing and each n occurs G(n) times, so Γ(G(1..m)) = G(1..G(1)+...+G(m)). Since
   R_2 = (1,2) = G(1..2), every R_k (k ≥ 2) is a prefix of G, and |R_{k+1}| = sum R_k, last(R_{k+1}) = |R_k|, so
   A014644(m+1) = |R_m|.
2. Let S_n = a(1) + ... + a(n). Claim: S_n + 1 = |R_{n+1}| (true for n = 1, 2). The triangle's rows 1..n are the
   first S_n terms of G with the second term removed. If the claim holds for n-1 and n, then G(1..S_n+1) = R_{n+1}
   and G(1..S_{n-1}+1) = R_n, so R_{n+1} is R_n followed by row n, hence sum(row n) = sum R_{n+1} - sum R_n = |R_{n+2}| - |R_{n+1}|, and
   S_{n+1} + 1 = S_n + sum(row n) + 1 = |R_{n+2}|.
3. Hence a(n) = |R_{n+1}| - |R_n| = A014644(n+2) - A014644(n+1) for n ≥ 2, and the last element of row n is the
   last term of R_{n+1}, which is A014644(n+1).

**Evidence.**
- Lean (Mathlib): [`A113676_mathlib.lean`](A113676_mathlib.lean). Main theorems `A113676_differences`
  (n ≥ 2 → a(n) = A014644(n+2) - A014644(n+1)), `A113676_final_one`, `A113676_final`. Golomb's sequence is
  `golomb`, read off the rows R_k; `golomb_unique` proves that every g with g(1) = 1, nondecreasing, and each
  n ≥ 1 occurring exactly g(n) times (`Set.ncard`) equals `golomb` on n ≥ 1, so the theorems are about A001462 as
  defined. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): builds the triangle and the Levine array; a(1..8) =
  1, 1, 2, 6, 27, 234, 6202, 1084009 (the entry's data) and both conjectures for rows 1..7.
- Outside Lean: none beyond reading the definitions. Not verified in Lean: agreement with the OEIS data terms.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry (last edited 2025) still states both conjectures. J. Claes and
R. Miyamoto, "Golombic and Levine sequences", arXiv:2602.10992 (2026), note step 1 (Γ maps the first n terms of
Golomb's sequence to its first A001463(n) terms) but do not mention A113676. No other source found (web search).
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
