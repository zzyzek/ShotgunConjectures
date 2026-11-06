# OEIS A156869 / A156870: T(2n + m, n + m) = T(2n, n) iff m >= 0

**Source.** [A156869](https://oeis.org/A156869): T(n,k) = number of nondecreasing sequences of n positive integers with
reciprocals adding up to k (1 <= k <= n). [A156870](https://oeis.org/A156870): a(n) = T(2n, n). Both entries state the
conjecture "A156869(2n + m, n + m) = a(n) if and only if m >= 0". A156869 also has the comment (F. T. Adams-Watters,
Feb 20 2009) that the diagonals are constant for n <= 2k, since such a sequence must contain a 1, and removing it gives a
sequence for (n-1, k-1). (OEIS text, checked 2026-11-06.)

**Reading.** m ranges over integers with n + m >= 1, so that T(2n+m, n+m) is an entry of the triangle.

**Result.** True in both directions: T(2n+m, n+m) = T(2n, n) for m >= 0, and T(2n+m, n+m) < T(2n, n) for m < 0.

**Argument.** Let S(N, K) be the set of sequences counted by T(N, K).
1. Prepending 1 maps S(N, K) injectively into S(N+1, K+1), so T(N, K) <= T(N+1, K+1) (all sets are finite: the least
   entry x of a sequence of length N with reciprocal sum s satisfies x <= N/s, and induct on N).
2. A sequence with no 1 has reciprocal sum at most (length)/2. So when N <= 2K every element of S(N+1, K+1) starts
   with 1, the map of step 1 is onto, and T(N+1, K+1) = T(N, K). Iterating from (2n, n) gives the "if" direction
   (this is Adams-Watters' remark).
3. For N = 2K - 1 the sequence of 2K twos lies in S(2K, K) and does not start with 1, so T(2K-1, K-1) < T(2K, K).
4. For m = -d < 0: T(2n-d, n-d) <= T(2n-1, n-1) by d-1 uses of step 1, and T(2n-1, n-1) < T(2n, n) by step 3.

**Evidence.**
- Lean (Mathlib): [`A156870_mathlib.lean`](A156870_mathlib.lean). `T n k` is `Set.ncard` of the lists of length n,
  pairwise <=, positive entries, sum of 1/x equal to k in ℚ; `A156870 n = T (2n) n`. Main theorem
  `A156869_conjecture : 1 ≤ n → 1 ≤ n + m → (T (2n+m).toNat (n+m).toNat = A156870 n ↔ 0 ≤ m)` (m : ℤ), from
  `diag_const` and `diag_lt`. Checked with `tools/leancheck-mathlib.sh`, no warnings; axioms propext,
  Classical.choice, Quot.sound; no sorry, no native_decide.
- [`certificate/brute.py`](certificate/brute.py): rows 1..6 of the triangle equal the data; the claim holds on them.
- Outside Lean: none. Not verified in Lean: agreement of `T` with the data terms (brute.py, rows 1..6).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: A156869 and A156870 entries (the "if" direction is Adams-Watters' 2009 comment;
the "only if" direction is not addressed), google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (no
entries). The strict inequality for m < 0 is ours and immediate.
