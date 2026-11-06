# OEIS A216971: every entry of row n is divisible by n

**Source.** [A216971](https://oeis.org/A216971) (Geoffrey Critzer, Sep 21 2012): T(n,k) is "the number of functions
f:{1,2,...,n}->{1,2,...,n} that have exactly k nonrecurrent elements mapped to some (one or more) recurrent
element", n >= 1, 0 <= k <= n-1. Comment: "Conjecture: every entry in row n is divisible by n. - _Jon Perry_, Sep 21
2012". (OEIS text, CC BY-SA 4.0, revision #43 of Aug 09 2022, checked 2026-11-06.)

**Reading.** x is recurrent for f if f^m(x) = x for some m >= 1 (the entry's comment). T(n,k) counts f with exactly
k elements x such that x is not recurrent and f(x) is recurrent. This reproduces rows 1..6 by brute force
(certificate/check.py).

**Result.** True: n divides T(n,k) for all n >= 1 and all k.

**Argument.** Let R(f) be the set of recurrent points; it is nonempty (n >= 1, finiteness) and f permutes it.
Fix r >= 1 and let S be the set of f with statistic k and |R(f)| = r.
1. *Double count.* Count pairs (f, x) with f in S and x in R(f): this is r|S|. Relabelling f by the transposition
   (x 0), f -> t f t^-1, keeps the statistic and |R|, and moves "x recurrent" to "0 recurrent". So the count is
   n M with M = #{f in S : 0 in R(f)}. Hence r|S| = nM.
2. *Factor r!.* For a fixed set R, the f with R(f) = R and statistic k correspond bijectively to pairs (pi, g):
   pi a permutation of R and g such a function that fixes R pointwise (replace f on R by the identity, and glue
   pi back). Replacing f on R by any map that permutes R does not change which points are recurrent (an orbit
   that enters R never leaves it, so a point outside R returns to itself only along an orbit that avoids R, where
   the two functions agree) nor the statistic (it reads f only off R). So r! divides the count for each R, and
   r! divides M.
3. With M = r! q, r|S| = n r (r-1)! q, so |S| = n (r-1)! q. Summing over r gives n | T(n,k).

Equivalently T(n,k) = sum_{r>=1} C(n,r) r! r^k C(m-1,k-1) m^(m-k) (m = n - r, k >= 1), and C(n,r) r! =
n!/(n-r)! is a multiple of n for r >= 1. certificate/check.py checks this formula against brute force (n <= 6) and
the b-file (rows 1..32); it is not used in the Lean proof.

**Evidence.**
- Lean (Mathlib): [`A216971_mathlib.lean`](A216971_mathlib.lean). `T n k` counts `f : Fin n → Fin n` with
  `stat f = k`, `stat f` the number of `x` with `¬ Rec f x ∧ Rec f (f x)`, `Rec f x := ∃ m, 0 < m ∧ f^[m] x = x`.
  Main theorem `A216971_main : 0 < n → n ∣ T n k`. Route: `T_eq_sum`, `S_zero` (a recurrent point exists,
  `exists_rec`), `double_count` (via `conj`, `stat_conj`, `recSet_conj`, `fiber_eq`), `fact_dvd_M` and
  `fact_dvd_A` (via `replace`, `permOf`, `glue`, `normal`), `S_dvd`. Check: `tools/leancheck-mathlib.sh`, exit 0,
  no warnings; axioms of every theorem at most propext, Classical.choice, Quot.sound. No `sorry`, no
  `native_decide`.
- [`certificate/check.py`](certificate/check.py): brute force of the definition for n <= 6; the closed formula
  against brute force and the b-file ([`certificate/b216971.txt`](certificate/b216971.txt), rows 1..32); all
  entries divisible by n.
- Outside Lean: none. Not verified in Lean: agreement of `T` with the OEIS data terms (check.py computes them from
  the same definition).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry and its history (to #43, Aug 09 2022) keep the conjecture with no
proof; the e.g.f. 1/(1 - x exp(y T(x))) - 1 is given but no divisibility argument. Not in
google-deepmind/formal-conjectures (no file for 216971) or otoi-lab/oeis-lean-proofs. A web search found no
proof. The argument is elementary.
