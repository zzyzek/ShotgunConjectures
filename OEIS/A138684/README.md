# OEIS A138684: Layman's self-similarity conjecture has the wrong peak values; the corrected form holds

**Source.** [A138684](https://oeis.org/A138684) (offset 1), first differences of
[A138683](https://oeis.org/A138683). A138683: "a(1)=1 and, for n>1, a(n) is the smallest integer
greater than a(n-1) such that a(n) and a(k) do not sum to a term of A001333". Comment in A138684 by
John W. Layman (Nov 26 2011): "Conjecture. Let x(1)=1, x(2)=2, x(n) = 2*x(n-1) + x(n-2), and let
y(1)=1, y(2)=3, y(n) = y(n-1) + y(n-2). Then if n=x(k), a(n)=y(k); if x(k) < n < 2*x(k),
a(n) = a(n-x(k)); and if 2*x(k) <= n < x(k+1), a(n)=1. (This has been confirmed for n < 500.)"
(OEIS text, CC BY-SA 4.0; A138684 revision #11 of Sep 11 2021, checked 2026-11-06.)

**Reading.** The name of A138683 says a(1) = 1, but its data are 2, 3, 6, 7, 8, 12, ... and the data
of A138684 are the differences of exactly this list. The greedy rule started at 2 reproduces both
data sections; started at 1 it gives 1, 3, 5, 7, 8, ... with differences 2, 2, 2, 1, 3, ..., which is
not A138684 (`certificate/readings.py`). We take a(1) = 2 for A138683, as the data do. Whether the
pair a(n) + a(n) is also forbidden does not change the sequence. A001333 = 1, 1, 3, 7, 17, 41, 99, ...;
x(k) are the Pell numbers 1, 2, 5, 12, 29, 70, ...; y(k) are the Lucas numbers 1, 3, 4, 7, 11, 18, ...

**Result.** False as stated: a(12) = 6 (in the entry's data), while x(4) = 12 and y(4) = 7. The peak
values a(x(k)) are 1, 3, 4, 6, 11, 23, 52, 122, ...; they agree with y(k) only for k = 1, 2, 3, 5.
The other two clauses are true, and the conjecture holds for every k >= 1 once y(k) is replaced by

  z(1) = 1,  z(k) = (A001333(k-1) + 5)/2 for k >= 2.

**Argument.** Let S be the set of terms of A138683, q_j = 1, 3, 7, 17, 41, ... (q_j = A001333(j+1)),
r_j = P_1 + ... + P_j (Pell P), so q_j = 2 r_j + 1 and q_{j+1} = 2 q_j + q_{j-1}. By the greedy rule,
x >= 2 is in S iff no smaller y in S has x + y in A001333.
1. *Local rule.* For x in [r_j + 1, r_{j+1}] we have q_j < 2x < q_{j+1} and every q_i with i < j is
   at most r_j + 1 <= x. So the only value of A001333 in (x, 2x) is q_j, and x is in S iff x >= q_j or
   q_j - x is not in S.
2. *Reflection.* For j >= 1 and 1 <= z <= r_{j+1}: z is in S iff not (z < q_j and q_j - z in S). For
   z > r_j this is step 1; for z <= r_j, step 1 applied to w = q_j - z (which lies in [r_j + 1, 2 r_j])
   says w is in S iff z is not.
3. *Level structure* (k = j + 1 >= 2, t = 2 P_k). Since q_k - t = q_{k-1}, step 1 at level k and
   step 2 give: z + t is in S iff z is in S, for 1 <= z <= r_k (copy); nothing in [r_k + 1, t] is in S
   (its reflections lie in [q_{k-1}, r_k], all in S by step 1); everything in [r_k + t + 1, r_{k+1}]
   is in S (it is >= q_k), a run of P_{k-1} integers.
4. *Counting.* By induction, exactly P_k terms are <= r_k, the last one r_k. So the terms with
   indices P_k + 1 .. 2 P_k are the first P_k terms plus 2 P_k, and indices 2 P_k .. P_{k+1} are the
   run. This gives a(n) = a(n - P_k) for P_k < n < 2 P_k, a(n) = 1 for 2 P_k <= n < P_{k+1}, and
   a(P_k) = (2 + 2 P_k) - r_k = (q_{k-2} + 5)/2 = (A001333(k-1) + 5)/2.

**Evidence.**
- Lean (Mathlib): [`A138684_mathlib.lean`](A138684_mathlib.lean). `inS` is the greedy set by
  well-founded recursion, `A138683 n = Nat.nth inS (n - 1)`, `A138684 n = A138683 (n+1) - A138683 n`.
  `A138683_greedy` and `A138683_unique` prove that this is the greedy sequence of the entry with first
  term 2 (any sequence obeying the greedy rule with f 1 = 2 equals it). Main theorems:
  `conjecture_false : ¬ Shape yc` (the conjecture literally, with Layman's x and y) and
  `A138684_shape : Shape zc` (the corrected form for all k >= 1). Route: `rule`, `reflect`, `copy`,
  `gap`, `run`, `inv`, `s_copy`, `s_P`, `s_run`, `A138684_at`, `A138684_mid`, `A138684_ones`.
  Checked with `tools/leancheck-mathlib.sh`: OK, no warnings; axioms propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): recomputes A138683 to 300000 (162097 terms),
  matches the 105 data terms of A138684, lists the failures of Layman's y (n = 12, 70, 169, ...) and
  finds no failure of the corrected form for k <= 14.
- [`certificate/readings.py`](certificate/readings.py): the sequence under the readings a(1) = 1 or 2
  and with or without the self-pair.
- Outside Lean: the choice a(1) = 2 (data) over a(1) = 1 (name) for A138683. Not verified in Lean:
  agreement of the Lean definition with the OEIS data terms (check.py does this from the same rule).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The A138684 entry and history (11 revisions) still carry the
comment as a conjecture with no correction; its own data contradicts it at n = 12. A138683 and A114889
/ A114890 (the analogous powers-of-3 problem, also a Layman conjecture) give no proof. Web search
(A138684, A138683, greedy sums avoiding A001333) and arXiv 2410.07237, 2603.09939, 2606.17447 (OEIS
conjecture and greedy-sequence papers) do not mention these sequences. Not in
google-deepmind/formal-conjectures (tree at HEAD 2026-11-06, no file for 138684) or
otoi-lab/oeis-lean-proofs.
