# OEIS A157308: a(m) is odd iff m = 0 or m is a power of 2

**Source.** [A157308](https://oeis.org/A157308) (Paul D. Hanna): g.f. A(x) with F(x) = A(x F(x)), F the g.f. of
[A155585](https://oeis.org/A155585) (e.g.f. exp(x)/cosh(x)); also A(x) = x / serreverse(x F(x)). Conjecture in the
entry: "a(m) == 1 (mod 2) iff m is a power of 2 or m=0" (Hanna, Mar 17 2009). (OEIS text, checked 2026-11-06.)

**Reading.** The %N line describes A by a zero pattern; the formulas and both programs compute A(x) =
x/serreverse(x F(x)), i.e. A is the unique series with A(x F(x)) = F(x). That is the definition used. It reproduces
the data (certificate/check.py, 28 terms).

**Result.** True.

**Argument.** Work mod 2.
1. F(x) = 1 + x (mod 2). From cosh(x) E(x) = exp(x): sum_{j even} C(n,j) f(n-j) = 1. By induction f(i) is odd only for
   i <= 1, so for n >= 2 the recurrence gives f(n) = 1 + [n even] + n [n odd] = 0 (mod 2).
2. Hence A(x + x^2) = 1 + x over GF(2). Put B = A - 1, so B(x + x^2) = x, and B is determined (x + x^2 has a
   compositional inverse).
3. T(x) = sum_{k>=0} x^(2^k) solves it: by Frobenius, T(x + x^2) = sum_k (x^(2^k) + x^(2^(k+1))) = x (telescoping).
   So A = 1 + T (mod 2), which is the claim.
Coefficientwise (the form checked in Lean): sum_{m<=n} a(m) C(m, n-m) = [n <= 1] mod 2, a triangular system, and
b(m) = [m = 0 or m = 2^k] solves it because C(2^k, j) is even for 0 < j < 2^k.

**Evidence.**
- Lean (Mathlib): [`A157308_mathlib.lean`](A157308_mathlib.lean). `f` (A155585) by the recurrence of
  exp(x)/cosh(x), with `f_egf` proving (∑ f(n)x^n/n!)·cosh = exp as power series over ℚ; `a` (A157308) by
  a(n) = f(n) − ∑_{m<n} a(m)[x^(n−m)]F^m, with `a_spec` proving ∑_{m≤n} a(m)[x^(n−m)]F^m = f(n), i.e. A(xF(x)) = F(x).
  Main theorem `A157308_conjecture : Odd (a m) ↔ m = 0 ∨ ∃ k, m = 2 ^ k`. Checked with
  `tools/leancheck-mathlib.sh`, no warnings; axioms propext, Classical.choice, Quot.sound; no sorry, no
  native_decide.
- [`certificate/check.py`](certificate/check.py): the same recurrences reproduce the 28 data terms and the parity
  pattern for m < 40.
- Outside Lean: none. Not verified in Lean: agreement with the data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: OEIS A157308, A157309, A157310 (still conjecture), web search, arXiv:2607.24832
and arXiv:2608.11941 (OEIS-conjecture proof collections; no mention), google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs (no entries). No proof found.
