# OEIS A108863: Motzkin transform of 0, 0, 0, A001651

**Source.** OEIS [A108863](https://oeis.org/A108863) (Dyck n-paths with exactly one UUUD, offset 0), comment by
R. J. Mathar (Dec 11 2008): "Conjecture: this is the Motzkin transform of the sequence of three zeros followed by
A001651."

**Reading.** Motzkin transform as Mathar describes it in A132894: substitute x → x·M(x) in the g.f., M = Motzkin g.f.
(A001006); coefficientwise a(n) = Σ_{k≤n} b_k [x^n](xM)^k. b = 0, 0, 0, 1, 2, 4, 5, 7, ... (A001651 = numbers not
divisible by 3, offset 1), with g.f. x³(1+x+x²)/((1−x)(1−x²)). A108863 is represented by the entry's g.f.
G = (x − 1 + (1−2x)M)/(x(1−3x)(1+xM)).

**Result.** True: the Motzkin transform of b has g.f. G, so equals A108863.

**Argument.** Substitution is a ring homomorphism, so with y = xM the transform A satisfies
A(1−y)(1−y²) = y³(1+y+y²). M = 1 + xM + x²M² gives y = x + xy + xy². Then
x(1−y)²·[x(1−3x)(1+y)A − (x − 1 + (1−2x)M)] = x²(1−3x)·[A(1−y)(1−y²) − y³(1+y+y²)] − q·(x + xy + xy² − y)
with q = −3x²y³ + xy³ − 3xy² + 3xy − x + y² − 2y + 1, and x(1−y)² ≠ 0 in the domain ℚ⟦x⟧.

**Evidence.**
- Lean (Mathlib): [`A108863_mathlib.lean`](A108863_mathlib.lean). `A108863_conjecture : X(1−3X)(1+X·M)·A108863_transform
  = X − 1 + (1−2X)M` with `A108863_transform = (Σ b_k x^k).subst (X·M)` (`PowerSeries.subst`);
  `A108863_unique` (any G with this equation is the transform); `A108863_transform_coeff` (the coefficient form);
  `A001651_eq` (A001651 via `Nat.nth` equals ⌊(3m−1)/2⌋); `A108863_B_eq`; `A108863_M_eq`.
  Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: transform vs the entry's 16 terms, vs the printed g.f., vs brute-force counts of Dyck paths
  with exactly one UUUD (n ≤ 11), and the polynomial identity with quotient q.
- Outside Lean: that the printed g.f. counts the Dyck paths (checked by enumeration for n ≤ 11); that the Motzkin
  recurrence used matches A001006's definition (standard).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: OEIS A108863 (g.f. printed, also V. Kotesovec's recurrence), A001651, A132894,
web search, google-deepmind/formal-conjectures (no file). No proof found.
