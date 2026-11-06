# OEIS A123721: first occurrences of k in A123249(n) - 2n

**Source.** [A123721](https://oeis.org/A123721) (Klaus Brockhaus, Oct 2006): a(n) = A123249(n) - 2n, where
[A123249](https://oeis.org/A123249)(1) = 1 and A123249(n) = n + (smallest integer >= n missing from the earlier
terms). "Conjecture: For k > 1, the smallest n such that a(n) = k is A123720(k) = 2^k + 2^(k-1) - k. Confirmed for
k <= 22." (OEIS text, revision #4 of Sep 02 2017, checked 2026-11-06.)

**Reading.** a(1): the data list a(1) = 1 (the PARI program prints A123249(1)); by the name a(1) = -1. Either way
n = 1 does not affect the claim for k > 1.

**Result.** Misstated by one index: the smallest n with a(n) = 2 is 9 = A123720(3), while A123720(2) = 4 and
a(4) = 1. Corrected and proved: for every k >= 1 the smallest n with a(n) = k is A123720(k+1) = 3·2^k - k - 1
(this matches the data and the "confirmed for k <= 22" check).

**Argument.** Let m(n) be the smallest integer >= n missing from a(1..n-1) (A123249 values) and d(n) = m(n) - n,
so A123249(n) = 2n + d(n) for n >= 2 and A123721(n) = d(n).
1. m is nondecreasing and A123249 is strictly increasing.
2. *Run.* If d(n) >= K + 1, then n, ..., n + K are earlier terms, consecutive in value, hence consecutive terms
   A123249(i), ..., A123249(i + K) with i < n, and d(i + t) = d(i) - t.
3. *Staircase.* If d(j) = k then m(j + t) = m(j) for t <= k, so A123249(j + t) = 2j + k + t; these are earlier terms
   at n = 2j + k, so d(2j + k) >= k + 1.
4. *Induction.* Let G(k) = 3·2^k - k - 1 and assume d(G(k)) = k and d(n) < k for n < G(k). By 3, d(2G(k) + k) >= k+1.
   If n < 2G(k) + k were the least n with d(n) >= k + 1, step 2 gives i < n with d(i) = d(i + k) + k >= k, and
   minimality gives d(i) = k, so i >= G(k) and n = 2i + k >= 2G(k) + k, a contradiction. Step 2 at n = 2G(k) + k
   also shows d(n) <= k + 1. So G(k+1) = 2G(k) + k is the first n with d(n) = k + 1.

**Evidence.**
- Lean (Mathlib): [`A123721_mathlib.lean`](A123721_mathlib.lean), namespace `OEIS_A123721`. `A123249` is the entry's
  definition (least missing integer via `Nat.find`), `A123721 n = A123249 n - 2n`. Main theorems
  `A123721_first k : A123721 (G k) = k ∧ ∀ n, 1 ≤ n → n < G k → A123721 n ≠ k` with `G k = 3·2^k - k - 1`
  (`G_eq_A123720`: G k = 2^(k+1) + 2^k - (k+1)), and `A123721_misstated` (a(4) = 1, a(9) = 2, a(n) ≠ 2 for n < 9).
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): computes the sequence to n = 3·10^6 and the first occurrences
  (k <= 19 equal 3·2^k - k - 1).
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the entry still says "Conjecture"; the linked Abrego, Fernandez-Merchant, Llano
paper (J. Integer Seq. 14 (2011) 11.7.4) concerns Macaulay functions and A123578-A123580, A123731, not this claim.
Not in google-deepmind/formal-conjectures (clone of 2026-11-06) or otoi-lab/oeis-lean-proofs (clone of 2026-10-13).
