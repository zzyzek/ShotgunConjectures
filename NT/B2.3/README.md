# Guy B2: Kravitz's "no odd-square abundance" conjecture is false (already in the book)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B2 (p. 75). Kravitz conjectured that no n has abundance σ(n) − 2n
equal to an odd square. The same paragraph of the book reports Graeme Cohen's
counterexamples, including five of the form n = 2²·7²·p², the first being the smallest such n.

**Result.** False, and the book itself already says so. The scan did not add a resolution;
this entry records the check. Smallest example: n = 2²·7²·53² = 550564,
σ(n) − 2n = 41209 = 203².

**Argument.** For n = 2²·7²·p² with p ≠ 2, 7 prime, σ(n) = 7·57·(p² + p + 1), so
σ(n) − 2n = 7(p² + 57p + 57). This is an odd square for p = 53, 277, 541, 153941 (search to
10^6), matching Cohen's list.

**Evidence.**
- Lean: [`B2_3.lean`](B2_3.lean) checks n = 550564, the value of σ(4)σ(49)σ(2809) and
  1142337 − 2·550564 = 203². Outside Lean: multiplicativity of σ.
- `certificate/misc_check.py`: the p-search and a brute-force divisor sum up to 2·10^6 showing
  550564 is the least n with odd-square abundance.

**Review level.** `lean-witness`. **Note:** answered in the source (Cohen); not a new result.
**Prior art.** G. L. Cohen, as cited in the book. 2026-11-01.
