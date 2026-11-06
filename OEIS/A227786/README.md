# OEIS A227786: positions of 2 in A227761

**Source.** [A227786](https://oeis.org/A227786) (A. Karttunen, Jul 31 2013): "Take squares larger than 1,
subtract 3 from even squares and 2 from odd squares", a(n) = (n+1)^2 - 2 - (n mod 2) = 1, 7, 13, 23, 33, 47, ...
Comment: "Conjecture: from n>=2 onward, a(n) gives the positions of 2's in A227761." The same conjecture
is in [A227761](https://oeis.org/A227761), which also asks "Are there any terms larger than 2?"
(OEIS text, CC BY-SA 4.0, revision #32 of A227786, checked 2026-11-06.)

**Reading.** A227183(x): read the binary runs of x from the least significant end, c1, c2, ..., ck; the
parts are c1, c1 + c2 - 1, c1 + c2 + c3 - 2, ... (A129594 coding). A227368(N) is the least x with
A227183(x) = N, and A227761(N) is the largest difference between successive parts of that partition
(0 for N < 2). This reading reproduces the b-files of A227368 and A227761 (N <= 132).

**Result.** True. For every N, A227761(N) = 2 exactly when N = a(n) for some n >= 2, i.e. N = j^2 - 2
with j >= 3 odd or N = j^2 - 3 with j >= 4 even. Also A227761(N) <= 2 for all N, which answers the
question in A227761: there are no terms larger than 2.

**Argument.** Write the code of a partition with k parts and largest part m from the top as runs
r_1, ..., r_k: r_t = (q_t - q_{t+1}) + 1 for t < k and r_k = q_k, where q_1 = m >= q_2 >= ... >= q_k are
the parts. The bit length is m + k - 1, and among codes of equal length the integer is smaller iff at
the first differing run an odd-numbered run is shorter or an even-numbered run is longer.
Put d_t = q_t - q_{t+1} (t < k) and D = mk - N = sum_t (k - t) d_t.

1. *Length.* Every N in [m + k - 1, mk] is the sum of a partition with k parts and largest part m, so
   the minimal code has m + k - 1 = L(N) = min{m' + k' - 1 : m'k' >= N}. If D >= m (or D >= k) the
   pair (m, k-1) (or (m-1, k)) would give a shorter code, so 0 <= D < min(m, k) for every pair (m, k)
   with m + k - 1 = L(N) and mk >= N. For N >= 4 also m, k >= 2.
2. *Greedy drops.* For fixed (m, k) the best code takes d_1 = 0, d_2 as large as possible, d_3 = 0,
   d_4 as large as possible, ..., and d_{k-1} = the remainder (weight 1). With D < k each greedy
   step on an even position with weight w >= 2 sees a remainder < w + 2, so d_t <= 1 there; the last
   drop (weight 1) is <= 2, and it is 2 exactly when k is odd and D = 2 (if D >= 3 the first even
   weight w <= D leaves D - w <= 1). So A227761(N) <= 2, with equality iff the winning pair has
   k odd and D = 2.
3. *Which pair wins.* Suppose the winner has k odd, D = 2, so its runs are 1^(k-2), 3, m-2.
   - m = k + 1: the pair (m+1, k-1) has D = 0 and runs 1^(k-2), m+1; position k-1 is even and
     m+1 > 3, so it is better.
   - m >= k + 3 or m <= k - 1: the neighbour (m-1, k+1) resp. (m+1, k-1) has D' = |m - k| + 1 >= 2 and
     its greedy drops put a 1 on an even position before k-1 (the weight there is the largest
     weight <= D' of the right parity, which is >= 2), where the original has 1; so it is better.
   - m = k gives N = k^2 - 2 and m = k + 2 gives N = (k+1)^2 - 3, both of the form a(n).
   Conversely, for N = j^2 - 2 (j odd >= 3) the valid pairs are (j, j) with D = 2 and (j +- 1, j -+ 1)
   with D = 1, and (j, j) beats both; for N = j^2 - 3 (j even >= 4) the valid pairs are (j+1, j-1) and
   (j-1, j+1) with D = 2 and (j, j) with D = 3, and (j+1, j-1) wins. In both cases the winner has
   k odd and D = 2.

**Evidence.**
- Lean (Mathlib): [`A227786_mathlib.lean`](A227786_mathlib.lean). Main theorem
  `A227786_conjecture (N) : A227761 N = 2 ↔ ∃ n, 2 ≤ n ∧ A227786 n = N`, with A227183, A227368
  (`Nat.find`), A227761 and A227786 defined from `Nat.digits 2` as in the entries. Steps 1-3 are
  `LL`, `F4`, `G_opt`, `G_max`, `dir1`, `dir2`; the integer comparison is `num_lt`. Axioms propext,
  Classical.choice, Quot.sound; no sorry, no native_decide.
- `certificate/rle.py`: minimal code by an exact search (bit length, then greedy runs with a
  feasibility test); `certificate/fast.py`: the pair/greedy model of steps 1-2;
  `certificate/compare.py . 600` checks rle.py against the b-files (N <= 132), fast.py against
  rle.py, no value > 2, and the positions of 2 against a(n), for N <= 600: all agree.
- Outside Lean: none (the agreement with the b-files is checked by the scripts only).

**Review level.** lean-proof.

**Prior art.** Checked 2026-11-06. The OEIS entries A227786 and A227761 still state the conjecture
and the question; no proof is linked. Not in google-deepmind/formal-conjectures (no
`FormalConjectures/OEIS/227786.lean` or `227761.lean`) or otoi-lab/oeis-lean-proofs. A web search
found only the OEIS pages.
