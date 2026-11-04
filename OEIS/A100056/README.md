# OEIS A100056: the A054065 permutations do not maximize the sum of differences

**Source.** [A100056](https://oeis.org/A100056) (sum of absolute differences of the A054065 permutation of 1..n),
comment: "Conjecture: a(n) provides the maximum sum of difference terms of any permutation of 1 through n. A054065
(or reversals) give the optimal permutations and a(n) gives the sum." (OEIS text, CC BY-SA 4.0.)

**Reading.** "Sum of difference terms" = Σ |π(i+1) − π(i)|; the entry's a(4) = 7 from (2,4,1,3) fixes this reading.

**Result.** False at n = 5: the A054065 row (5,2,4,1,3) gives 10, but (4,2,5,1,3) gives 2 + 3 + 4 + 2 = 11.
For n ≤ 9 the true maxima are 1, 3, 7, 11, 17, 23, 31, 39 = ⌊n²/2⌋ − 1 (A047838), against a(n) = 1, 3, 7, 10, 16,
22, 27, 37.

**Evidence.**
- Lean: [`A100056.lean`](A100056.lean): both sums and that both lists are permutations of 1..5. Outside Lean:
  that (5,2,4,1,3) is the A054065 row for n = 5 (listed in A054065; recomputed in `certificate/check.py`).
- `certificate/check.py`: brute force over all permutations, n ≤ 9.
- Lean (Mathlib): [`A100056_mathlib.lean`](A100056_mathlib.lean), `A100056_main`: (5,2,4,1,3) is the unique ordering of 1..5 with Int.fract(h·φ) increasing (the A054065 row, φ = `goldenRatio`), its sum of absolute differences is 10, and (4,2,5,1,3) is a permutation with sum 11. So the A054065 row is now checked in Lean too; nothing outside Lean.

**Review level.** `lean-proof` for the disproof (Mathlib file above).
**Prior art.** Partly known: the maximum of the sum of |pi(i+1) - pi(i)| over permutations, floor(n^2/2) - 1, is folklore (it appears in programming-contest material; [A047838](https://oeis.org/A047838) gives the same values); that A054065 misses it from n = 5 is not recorded. [A100056](https://oeis.org/A100056) is unchanged since 2012. Searched OEIS entries, references and history, web. Checked 2026-11-04.
