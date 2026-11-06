# OEIS A079267: the number of short pairs in a random perfect matching of [2n] tends to Poisson(1)

**Source.** OEIS [A079267](https://oeis.org/A079267), d(n, s) = number of perfect matchings on {1, ..., 2n}
with s short pairs (pairs {i, i+1}). Comment: "Conjecture: Asymptotically, the n-th row has a Poisson
distribution with mean 1." (D. Callan, Nov 11 2012). (OEIS text, CC BY-SA 4.0, revision #91 of Mar 23 2026;
still marked conjecture on 2026-11-06.)

**Reading.** Divide row n by its sum (2n-1)!! (A001147). The claim is d(n, s)/(2n-1)!! → e^(-1)/s! for every
fixed s as n → ∞, i.e. the number S_n of short pairs in a uniform random perfect matching of [2n] converges in
distribution to Poisson(1).

**Result.** True; known (G. Kreweras and Y. Poupard 1978: all factorial moments of S_n tend to 1).

**Argument.**
1. *Factorial moments.* E[S_n (S_n - 1) ... (S_n - k + 1)] counts ordered k-tuples of distinct short pairs all
   present. A set of k disjoint short pairs {i, i+1} in [2n] is a choice of k non-overlapping dominoes on a path of
   2n vertices: C(2n-k, k) ways. Given the set, the other 2n - 2k points are matched in (2n-2k-1)!! ways. So
   sum_s C(s, k) d(n, s) = C(2n-k, k) (2n-2k-1)!!, and the k-th factorial moment is
   F_k(n) = k! C(2n-k, k) (2n-2k-1)!!/(2n-1)!! = prod_{i<k} (2n-k-i)/(2n-1-2i).
2. *Limit.* Each of the k factors is at most 1 (2n-k-i ≤ 2n-1-2i for i ≤ k-1) and tends to 1, so
   0 ≤ F_k(n) ≤ 1 and F_k(n) → 1 = the k-th factorial moment of Poisson(1).
3. *Poisson law.* By inclusion–exclusion (Bonferroni), P(S_n = s) = (1/s!) sum_{j=0}^{n-s} (-1)^j F_{s+j}(n)/j!
   (this is the entry's explicit formula). With 0 ≤ F ≤ 1 the terms are dominated by 1/(s! j!), so termwise
   limits give P(S_n = s) → (1/s!) sum_j (-1)^j/j! = e^(-1)/s!.

**Evidence.**
- Lean (core): [`A079267.lean`](A079267.lean). `A079267_mt` lists matchings of {0, ..., 2n-1} by pairing the
  first point with each later point; `A079267_rows` (rows n ≤ 5 equal the OEIS rows) and `A079267_fmoment`
  (the factorial-moment identity of step 1 for n ≤ 5, all k ≤ n), both by `decide +kernel`, no axioms.
- [`certificate/check.py`](certificate/check.py): rows from R. J. Mathar's recurrence for n ≤ 80 satisfy the
  identity of step 1; total-variation distance to Poisson(1) is 0.0299, 0.0144, 0.0071, 0.0035, 0.0017 at
  n = 5, 10, 20, 40, 80.
- Outside Lean: steps 1–3 for general n (the domino count, the bounds on F_k, dominated convergence), and that
  `A079267_mt` enumerates each matching once for n > 5.

**Review level.** `lean-witness` (finite facts only; the theorem is from the literature, re-derived above).

**Prior art.** Checked 2026-11-06: D. Young, "Bubbles in linear chord diagrams" (arXiv:2408.17232), p. 1, states
that Kreweras and Poupard [Publ. ISUP 23 (1978) 57–74, scan linked from A000806] "showed further that all higher
factorial moments of the distribution approach 1", establishing the Poisson limit. The 1978 paper itself was not
read here. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones).
