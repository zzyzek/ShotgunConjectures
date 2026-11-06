# OEIS A195673: p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x)

**Source.** [A195673](https://oeis.org/A195673), Paul Curtz, Sep 23 2011: "Triangle T(n,k) read by rows:
T(0,0)=-2, T(1,0)=3, T(1,1)=0 and T(n,k) = T(n-1,k)-T(n-2,k-2) otherwise." Comment: the row polynomials
p(n,x) = sum_{k=0..n} T(n,k) x^(n-k), built with other initial constants T(0,0) = p and T(1,0) = q, satisfy
p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x), the S-polynomials of [A053119](https://oeis.org/A053119) (Chebyshev S:
S(0) = 1, S(1) = x, S(n) = x S(n-1) - S(n-2)). (OEIS text, CC BY-SA 4.0, revision #18 of Mar 30 2012, checked
2026-11-06.)

**Reading.** Entries outside 0 <= k <= n are 0, and T(1,1) = 0 is kept for every (p, q). The "otherwise"
recurrence then holds for every n >= 2 and every k (it returns 0 outside the triangle).

**Result.** True for all integers p, q and all n >= 0.

**Argument.** Shifting the sum index, sum_k T(n-2,k-2) x^(n-k) = p(n-2,x), so the row polynomials satisfy
p(n,x) = x p(n-1,x) - p(n-2,x) for n >= 2, with p(0,x) = p and p(1,x) = q x. The recurrence for T is linear in
(p, q), so T_{p+1,q+1} = T_{p,q} + T_{1,1} entrywise, and the difference of the row polynomials is the row
polynomial for p = q = 1. That one starts 1, x and has the S recurrence, so it is S(n,x).

**Evidence.**
- Lean (Mathlib): [`A195673_mathlib.lean`](A195673_mathlib.lean). `T p q n k` is the entry's recurrence with
  initial constants p, q; `a = T (-2) 3`; `rowPoly p q n = Σ C (T p q n k) X^(n-k)`; S is Mathlib's
  `Polynomial.Chebyshev.S ℤ`. Main theorem `A195673_conjecture : rowPoly (p+1) (q+1) n - rowPoly p q n =
  Chebyshev.S ℤ n`; coefficientwise `A195673_coeff`; `A195673_data` checks the 71 data terms by `decide`. Route:
  `T_lin`, `T_neg`, `T_big`, `rowPoly_rec`, `rowPoly_one_one`. Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check_A195673.py`](certificate/check_A195673.py): the data terms, and the identity coefficientwise
  for p, q in [-5, 5], n <= 30.
- Outside Lean: none. The identification of A053119's S(n,x) with Mathlib's `Chebyshev.S` is by the recurrence
  S(n) = x S(n-1) - S(n-2), S(0) = 1, S(1) = x stated in A053119.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry and its history (revisions #9 to #18) give the identity only as a
conjecture, with the examples A192011 - A135929 = A053119. A web search found no proof; the identity is immediate
from linearity. Not in google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/195673.lean`) or
otoi-lab/oeis-lean-proofs (files A384222, A400194, A8578 only).
