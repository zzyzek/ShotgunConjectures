# OEIS A054096: column 2 of A054090 is A006183 shifted right

**Source.** [A054096](https://oeis.org/A054096) (offset 2), "T(n,2), array T as in A054090", comment by
Ralf Stephan (Jan 15 2004): "Conjecture: sequence is A006183 shifted right." Array
[A054090](https://oeis.org/A054090): "T(n,0) = 1 for n >= 0, T(n,1) = r(n-1), T(n,k) = T(n,k-1) -
(-1)^k * r(n-k) for k = 2, 3, ..., n, n >= 2, r(h) = sum of the numbers in row h of T."
[A006183](https://oeis.org/A006183) (offset 1): "a(n) = (n+1)*a(n-1) + (2-n)*a(n-2)", data 1, 2, 6,
22, 98, ... (OEIS text, CC BY-SA 4.0; A054096 revision #6, A054090 #16, A006183 #33, checked
2026-11-06.)

**Reading.** The recurrence in the name of A006183 is written for a[0] = 1, a[1] = 2 (the entry's
Mathematica program); with the entry's offset 1 it reads a(1) = 1, a(2) = 2, a(n) = n a(n-1) +
(3-n) a(n-2) (the entry's Magma program), which reproduces the data. "Shifted right" means
A054096(n) = A006183(n-1) for n >= 2, which matches all 18 data terms.

**Result.** True: A054096(n) = A006183(n-1) for every n >= 2.

**Argument.** Write r(h) for the row sums.
1. For 2 <= k <= m+1: T(m+1,k) + T(m,k-1) = r(m). For k = 2 both sides equal T(m+1,1) = r(m)
   (the r(m-1) terms cancel); going from k to k+1 adds -(-1)^(k+1) r(m-k) - (-1)^k r(m-k) = 0.
2. Summing row m+1: r(m+1) = 1 + r(m) + sum_{k=2}^{m+1} (r(m) - T(m,k-1)) = 1 + r(m) + m r(m) -
   (r(m) - 1) = m r(m) + 2. (This recurrence for A054091 is stated in that entry by G. Detlefs, 2010,
   without proof.)
3. T(m+2,2) = T(m+2,1) - r(m) = r(m+1) - r(m). With b(m) = r(m+1) - r(m) we get b(0) = 1, b(1) = 2,
   and step 2 gives b(m+2) = (m+3) b(m+1) - m b(m) (the difference of the two sides is
   [r(m+3) - (m+2)r(m+2) - 2] - 2[r(m+2) - (m+1)r(m+1) - 2] + [r(m+1) - m r(m) - 2] = 0). This is the
   recurrence of A006183 at index m+3, so b(m) = A006183(m+1), i.e. A054096(n) = A006183(n-1).

**Evidence.**
- Lean (Mathlib): [`A054096_mathlib.lean`](A054096_mathlib.lean). `T` follows the A054090 rule
  literally (well-founded recursion), `r n` = row sum, `A054096 n = T n 2`, `A006183` by the
  recurrence with the data's initial terms. Main theorem `A054096_eq_A006183_shift : 2 ≤ n →
  A054096 n = A006183 (n - 1)`; steps `pair`, `r_succ`, `T_two`, `T_two_eq`. Checked with
  `tools/leancheck-mathlib.sh`: OK, no warnings; axioms propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): builds T from the definition for n <= 60, matches
  the data of A054096 and A006183, and checks the identity and the row-sum recurrence.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. A054096 still lists the comment as a conjecture (history: no
change since 2004). A054091 states the row-sum recurrence r(n) = (n-1)r(n-1) + 2 (Detlefs, 2010) and
M. Somos's PARI program in A054090 (2006) encodes the resulting closed form, both without proof; the
link to A006183 is then two lines. Web search found no written proof. Not in
google-deepmind/formal-conjectures (tree at HEAD 2026-11-06) or otoi-lab/oeis-lean-proofs.
