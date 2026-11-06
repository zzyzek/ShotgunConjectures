# OEIS A170941: involutions without adjacent transpositions, proportion → 1/e

**Source.** [A170941](https://oeis.org/A170941) (offset 0), a(n+1) = a(n) + n·a(n−1) − a(n−2) + a(n−3),
a(0..3) = 1, 1, 1, 2. Comment (David Callan, Nov 11 2012): a(n) is the number of involutions on [n] that contain no
adjacent transposition, and "Conjecture: a(n)/A000085(n) -> 1/e as n -> inf." (OEIS text, CC BY-SA 4.0; still a
conjecture in revision #52, May 30 2026, checked 2026-11-06.)

**Result.** True: a(n)/I(n) → e^(−1), where I(n) = A000085(n) is the number of involutions of [n].

**Argument.** Write I(0) = I(1) = 1, I(m+2) = I(m+1) + (m+1) I(m).
1. *Inclusion–exclusion.* Let b(n) = Σ_k (−1)^k C(n−k, k) I(n−2k). C(n−k, k) counts sets of k pairwise disjoint
   adjacent pairs {i, i+1} in [n]; the involutions containing all of them as 2-cycles are the involutions of the other
   n − 2k points. So b(n) counts involutions of [n] with no adjacent transposition (this is Callan's comment).
2. *b satisfies the A170941 recurrence.* With K(n) = Σ_k k (−1)^k C(n−k, k) I(n−2k):
   - k·C(m−k, k) = (m−k)·C(m−k−1, k−1) and a shift k → k+1 give K(m+2) = K(m) − (m+1) b(m);
   - Pascal's rule C(n+2−k, k) = C(n+1−k, k) + C(n+1−k, k−1), the recurrence of I, and
     (n+1−2k) C(n+1−k, k) = (n+1−k) C(n−k, k) give b(n+2) = b(n+1) + n b(n) − K(n).
   Eliminating K: b(n+4) = b(n+3) + (n+3) b(n+2) − b(n+1) + b(n). Since b(0..3) = 1, 1, 1, 2, a = b.
3. *Domination.* I(m+2) ≥ (m+1) I(m), so by induction on k,
   (n−k)(n−k−1)⋯(n−2k+1) · I(n−2k) ≤ I(n). Hence the k-th term of b(n)/I(n), namely
   (−1)^k/k! · (n−k)_k I(n−2k)/I(n), has absolute value ≤ 1/k!.
4. *Termwise limit.* (m+1) I(m)² ≤ I(m+1)² (two-step induction), hence I(m+1)² ≤ 2(m+1) I(m)², so
   q(m) = I(m+1)/((m+1) I(m)) ≤ √(2/(m+1)) → 0. Then (m+1−k) I(m)/I(m+2) = (1 − k/(m+1))/(1 + q(m)) → 1, and by
   induction on k, (n−k)_k I(n−2k)/I(n) → 1 for each fixed k.
5. *Tannery.* By dominated convergence for series, b(n)/I(n) → Σ_k (−1)^k/k! = e^(−1).

**Evidence.**
- Lean (Mathlib): [`A170941_mathlib.lean`](A170941_mathlib.lean), namespace `A170941`. `inv` = A000085 by its
  recurrence, `a` = A170941 by the entry's recurrence (over ℤ), `t n k = (−1)^k C(n−k,k) inv(n−2k)`,
  `b n = Σ_{k ≤ n} t n k`. Theorems: `K_rec`, `b_rec2`, `b_rec4`, `a_eq_b` (step 2); `desc_bound` (step 3);
  `inv_lower`, `inv_upper`, `q_tendsto`, `ratio_tendsto`, `E_tendsto` (step 4);
  `A170941_tendsto : Tendsto (fun n => (a n : ℝ) / inv n) atTop (𝓝 (Real.exp (-1)))` (step 5, Mathlib
  `tendsto_tsum_of_dominated_convergence`, `NormedSpace.expSeries_div_hasSum_exp`).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms of every theorem: at most propext,
  Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): brute-force count of involutions without adjacent transpositions
  for n ≤ 10 equals the recurrence; recurrence = inclusion–exclusion sum for n ≤ 500; recurrence = entry data
  a(0..27); a(n)/I(n) = 0.4029 at n = 100 and 0.3840 at n = 500 (slow approach, error of order n^(−1/2)).
- Outside Lean: step 1 (that b(n), equivalently A170941, counts involutions without adjacent transpositions). The
  Lean theorem is about the sequence defined by the entry's recurrence, which is the entry's definition.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry gives Kotesovec's asymptotic a(n) ~ exp(√n − n/2 − 5/4) n^(n/2)/√2
(stated without proof); with the classical I(n) ~ exp(√n − n/2 − 1/4) n^(n/2)/√2 it would give the limit, but no
derivation is cited. The recurrence is Stadler–Haslinger (1997), Theorem 5. A217876 (distribution of adjacent
transpositions in involutions) carries the companion conjecture that the distribution is asymptotically Poisson(1);
the same domination argument on factorial moments should give it, not done here. Web search (involutions without
adjacent transpositions, Hosoya index of the path complement) found no proof. Not in google-deepmind/formal-conjectures
(no `FormalConjectures/OEIS/170941.lean`, 2026-11-06).
