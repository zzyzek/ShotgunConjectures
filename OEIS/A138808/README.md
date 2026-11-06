# OEIS A138808: the row sums of A010766 are upper bounds

**Source.** [A138808](https://oeis.org/A138808) (Jonas Wallgren, May 16 2008): "Number of integer
pairs (x,y), x > 0, y > 0, such that x <= p, y <= q for any factorization n = p*q." Comment:
"Conjecture: the row sums of the plane partitions A010766 are upper bounds. - R. J. Mathar, Aug 06
2008". [A010766](https://oeis.org/A010766): row n is floor(n/k), k = 1..n. (OEIS text CC BY-SA 4.0,
checked 2026-11-06.)

**Reading.** "for any factorization" means "for some factorization" (the example a(8) = 20 is the
union of the rectangles 1 x 8, 2 x 4, 4 x 2, 8 x 1). The conjecture: a(n) <= sum_{k=1..n} floor(n/k)
(= A006218(n)).

**Result.** True for every n >= 1.

**Argument.** If x <= p, y <= q and pq = n then xy <= n. So every counted pair lies in
{(x,y) : x, y >= 1, xy <= n}, which has sum_{x=1..n} floor(n/x) elements (for fixed x the y are
1..floor(n/x)).

**Evidence.**
- Lean (Mathlib): [`A138808_mathlib.lean`](A138808_mathlib.lean). `A138808 n` is the `Set.ncard` of
  the entry's set of pairs; main theorem `A138808_le_rowSum : A138808 n ≤ ∑ k ∈ Icc 1 n, n / k`,
  for all n. Axioms propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): the definition reproduces the 24 data terms;
  the bound holds for n <= 2000, with equality exactly at n = 1, 2, 3, 4, 6, 8, 12, 24 in that range
  (observed only).
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry and history (later comments by R. Sigrist 2017 and
C. W. Wu 2026 give formulas but do not address the bound); not in google-deepmind/formal-conjectures
or otoi-lab/oeis-lean-proofs. The argument is immediate.
