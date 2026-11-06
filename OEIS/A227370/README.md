# OEIS A227370: an involution made of the transpositions (2k-1, 2k), k in A061887

**Source.** [A227370](https://oeis.org/A227370) (A. Karttunen, 2013): "Permutation which maps between A227368 and
A227369", a(n) = A227183(A227369(n)). Comments: "Conjecture 1: This is an involution ... Conjecture 2: (which would
automatically imply the conjecture 1): the only transpositions (used to compose the permutation) are of adjacent
terms 2k-1 and 2k, where A061887 gives the values of k. This is true at least for the first 35 transpositions (up
to k=60)." A227368(N) is the least x whose run-length partition (A227183) sums to N; A227369 is A227368 sorted.
A061887 = numbers in [2j^2, 2j^2 + 2j]. (OEIS text, revision #14, checked 2026-11-06.)

**Reading.** As in [OEIS/A227786](../A227786/README.md): the code of a partition with k parts and largest part m
has m + k - 1 bits; read from the top it has runs r_1, ..., r_k (r_1 a run of 1s, then alternating), with
r_t = d_t + 1 for t < k (d_t the drops) and r_k = smallest part. a(n) is the N whose minimal code is the n-th
smallest minimal code.

**Result.** Both conjectures are true. Let c(N) = A227368(N). For N ≥ 2, c(N) < c(N-1) exactly when N is even
and s^2 ≤ N ≤ s^2 + 2s for some even s ≥ 2 (that is N = 2k, k in A061887, k ≥ 2), and the codes sorted
increasingly are c(0), c(1), ... with exactly these adjacent pairs swapped. So A227370 is the product of the
disjoint transpositions (2k-1, 2k), k in A061887, k ≥ 2, hence an involution.

**Argument.** From A227786 (Lean-proved there: `LL`, `F4`, `G_opt`): the minimal code has length
L(N) = min{m + k - 1 : mk ≥ N}; it is the best, over the pairs (m, k) with m + k - 1 = L(N) and D = mk - N ≥ 0
(then D < min(m, k)), of the greedy code: d_t = 0 at odd t < k-1, the first even t < k-1 with k - t ≤ D gets
d_t = 1, and d_{k-1} takes the rest. Codes of different lengths are ordered by length, and L is nondecreasing.

1. *Shape of a candidate.* Compare each code with the alternating word 1010... . A candidate either first deviates
   with a 0 for a 1 (sign −) at the odd bit φ = least odd number ≥ k - D + 1 (a doubled 0-run at the even run
   p = φ - 1, or the final 0-run when D = 0 and k is even, or a lengthened run k-1 when k is odd and D ≤ 2), or,
   when k - D is odd and D ≤ 1, first deviates with a 1 for a 0 (sign +). The smaller code is the one with the
   earlier sign − deviation; sign + candidates lose to any sign − candidate.
2. *Blocks.* L = 2s - 1 for N = s^2 - E (0 ≤ E ≤ s - 1), pairs (s ± j, s ∓ j) with D = E - j^2; L = 2s for
   N = s^2 + s - E (0 ≤ E ≤ s - 1), pairs (s + 1 + j, s - j), (s - j, s + 1 + j) with D = E - j(j + 1). By step 1
   only k in {s - 1, s, s + 1} can reach the least φ; comparing the runs after the common deviation (first
   difference at run s - 1 or s - 2, whose bit value is its parity) gives the winners (m, k):
   - O, s - E even: (s + 1, s - 1) if s is odd, (s, s) if s is even;
   - O, s - E odd: E = 0: (s, s); E = 1: (s - 1, s + 1); E = 2: (s, s); E ≥ 3: (s + 1, s - 1) if s is even,
     (s, s) if s is odd;
   - V, s - E even: (s + 1, s); V, s - E odd: (s, s + 1) if s is even or E = 0, (s + 2, s - 1) if s is odd.
3. *Consecutive codes.* Group the N of a block by the doubled-run position p. Within a group of two (E, E - 1)
   the codes agree up to the end of the alternating middle part; the next bits decide: in O-blocks with s odd and
   V-blocks with s even the larger N has the smaller code (its tail is 0s, the other's 1s or 001...), in O-blocks
   with s even and V-blocks with s odd the order agrees with N; in O-blocks with s even the only inversion is the
   pair (s^2 - 1, s^2) (E = 1 has a sign + deviation, E = 0 the final 0-run). Groups with a smaller p deviate
   earlier, so every code of a group is below every code of the next group. The inversions are therefore exactly
   the even N in (s(s-1), s^2] for odd s, in (s^2, s^2 + s] for even s, and N = s^2 for even s; for even s these
   make up the even N in [s^2, s^2 + 2s].

**Evidence.**
- [`certificate/check.py`](certificate/check.py) (with [`certificate/fast.py`](certificate/fast.py) from A227786):
  for N ≤ 3000, the model reproduces the A227368 b-file (N ≤ 132), the winning pairs follow the case table of
  step 2, c(N) < c(N - 1) exactly on the stated set, the sorted order is the product of the transpositions, and
  it agrees with the A227370 b-file.
- Lean (Mathlib, partial): [`A227370_mathlib.lean`](A227370_mathlib.lean) (a copy of the A227786 model file plus
  section `A227370`). Checked: the in-pair comparisons of step 3 for explicit run lists in all four block types
  (`pair_V_even`, `pair_O_odd`: inversions; `pair_V_odd`, `pair_O_even`: no inversion) and the group order
  (`cross_group`), as inequalities between `num` of run lists via `num_lt`; and the bridge `min_struct`: for
  N ≥ 4, A227368(N) = num(R m δ) with greedy drops δ = G true k1 D, D = m(k1+1) − N < min(m, k1+1), and minimal
  bit length m + k1 over all m'k' ≥ N. Check: `tools/leancheck-mathlib.sh`,
  exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound.
- Outside Lean: step 2 beyond `min_struct` (which of the pairs (m, k) of minimal length wins, i.e. the winner table: closed forms of the greedy lists and the first-deviation comparison over all pairs), the small
  cases E ≤ 3 and the block-boundary pairs, and the assembly into the statement about A227370 (sorted order is
  the product of the transpositions). The model itself (minimal length, D < min(m, k), greedy drops, `num_lt`)
  is Lean-proved in `OEIS/A227786/A227786_mathlib.lean`.

**Review level.** `rechecked`.

**Prior art** (2026-11-06). OEIS A227370, A227368, A227369, A061887 (conjectures stated, checked to k = 60);
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs: no file. The argument is ours, built on the
A227786 model in this repository.
