# OEIS A227345: a distinct-part partition of n with boundary size k exists iff 3k^2/4 <= n

**Source.** [A227345](https://oeis.org/A227345), triangle T(n, k), 1 <= k <= n: number of partitions of n into
distinct parts with boundary size k, where the boundary size counts the parts p for which not both p-1 and p+1
are parts. Comment: "Conjecture: there exists a partition (into distinct parts) of n with boundary size k if and
only if 0 < k^2 * 3/4 <= n. - _Patrick Devlin_, Jul 13 2013" (OEIS text, CC BY-SA 4.0; still a conjecture in
revision #32, May 15 2025, checked 2026-11-06).

**Result.** True. For n >= 1, T(n, k) > 0 iff k >= 1 and 3k^2 <= 4n. Equivalently, the least n with boundary
size k is ceil(3k^2/4) (3m^2 for k = 2m, 3m^2 + 3m + 1 for k = 2m + 1), and every larger n also occurs. This also
proves the formula a(n) = floor(2 sqrt(n/3)) of A227568 (largest boundary size for n), stated there without proof.

**Argument.** Let S be the set of parts and B its boundary parts, |B| = k.
1. *No three consecutive boundary parts.* If x, x+1, x+2 are all in B, then x+1 has both neighbours in S, so it is
   not a boundary part.
2. *Counting.* A set of positive integers up to M with no three consecutive integers has at most (2M+2)/3
   elements (strip off M-2, M-1, M, of which at most two occur, and induct).
3. *Sum.* For such a set B with k elements, 4 * sum(B) >= 3k^2 + (k mod 2). Induct by removing the largest element
   M: by step 2, 2M >= 3k - 2, and 2M >= 3k - 1 when k is odd. Hence n = sum(S) >= sum(B) >= 3k^2/4. Also k >= 1,
   since the largest part is always a boundary part.
4. *Construction.* Let A_m = {1, 2, 4, 5, ..., 3m-2, 3m-1} (pairs {3j+1, 3j+2}, j < m): sum 3m^2, boundary size 2m.
   Boundary size is additive over pieces separated by a missing integer. For k = 2m and n >= 3m^2 take
   A_{m-1} ∪ {3m-2, b} with b = n - 3(m-1)^2 - (3m-2) >= 3m-1. For k = 2m+1 and n >= 3m^2 + 3m + 1 take
   A_m ∪ {c} with c = n - 3m^2 >= 3m+1.

**Evidence.**
- Lean (Mathlib): [`A227345_mathlib.lean`](A227345_mathlib.lean), namespace `A227345`. `bdry S` = number of
  p in S with not (p-1 in S and p+1 in S); `T n k` = number of subsets of {1..n} with sum n and `bdry` k (the
  entry's definition). Main theorems `A227345_conjecture : 0 < n → (0 < T n k ↔ 0 < k ∧ 3 * k ^ 2 ≤ 4 * n)` and
  `A227345_conjecture_real` (the entry's wording 0 < k^2 * 3/4 <= n over ℝ). Steps: `card_le` (2), `sum_bound`
  (3), `le_of_exists` (1 and 3), `A_sum`, `A_bdry`, `bdry_union`, `exists_of_le` (4).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms of every theorem: propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py) (argument: the b-file): brute-force T(n, k) equals the b-file rows
  for n <= 30; T(n, k) > 0 iff 3k^2 <= 4n on b-file rows n <= 100; the step-4 witnesses are valid for n <= 400.
- Outside Lean: none (the agreement of `T` with the entry's data is checked by `certificate/check.py` only).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still lists the conjecture; its history shows no proof. A227568
(largest boundary size) states a(n) = floor(2 sqrt(n/3)) without proof or attribution, which is the "only if"
direction plus the minimum. Web search (boundary size, distinct parts, Devlin) found no proof. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06).
