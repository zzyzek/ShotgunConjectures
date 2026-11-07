# OEIS A065056: partial sums of Recaman's sequence are at least n(n+1)/4, so no exponent c < 2 bounds them

**Source.** [A065056](https://oeis.org/A065056): partial sums of Recaman's sequence A005132. The scan's source
(OEIS wiki conjecture list, 2013) records the comment "Conjecture : there is a constant c=1.9... such that
a(n)/n^c is bounded." The current entry instead carries "Conjecture: lim n-->oo a(n)/n^2 exists and is about
0.8..." (Benoit Cloitre, May 04 2020). (OEIS text, CC BY-SA 4.0, fetched 2026-11-07.)

**Result.** The c = 1.9... conjecture is false: 4 a(n) >= n(n+1) for every n, so a(n)/n^c >= n^{2-c}/4 is
unbounded for every c < 2. (Cloitre's later limit conjecture, consistent with this, stays open: the upper bound
a(n) = O(n^2) would need R(k) = O(k) on average, which is not known.)

**Argument.** Write R for A005132. Each step is R(k) = R(k-1) - k (only when this is >= 0) or R(k) = R(k-1) + k,
so R(k-1) + R(k) >= k in both cases. Induction gives n(n+1) + 2R(n) <= 4 a(n): the step from n to n+1 adds
4R(n+1) on the right and 2(n+1) + 2R(n+1) - 2R(n) on the left, and 2(n+1) <= 2R(n) + 2R(n+1).

**Evidence.**
- Lean (core): [`A065056.lean`](A065056.lean). `st`, `R` (A005132 as defined: subtract if nonnegative and
  unseen), `A065056`; `R_first`, `A065056_first` (first ten terms match the entry), `R_pair`
  (n+1 <= R(n) + R(n+1)), `A065056_lower` (n(n+1) <= 4 a(n), all n). `tools/leancheck.sh`: OK, no warnings,
  axioms propext, Quot.sound; no sorry, no native_decide.
- [`certificate/check.py`](certificate/check.py): a(n)/n^2 = 0.841, 0.826, 0.864, 0.868, 0.859 at
  n = 10^3..10^7 (consistent with Cloitre's 0.8...).
- Outside Lean: none. Not verified in Lean: the real-number step "n^{2-c} is unbounded for c < 2".

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07. The c = 1.9 comment was superseded in the entry by Cloitre's n^2 conjecture
(2020), which already implies it is false, but no proof of the lower bound is given there. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).
