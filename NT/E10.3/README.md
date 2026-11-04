# Guy E10: Moser's base-3 collinearity question follows from density Hales–Jewett

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section E10. Moser maps n = Σ a_i 3^i to the lattice point (a₀, a₁, …) and
calls integers collinear if their images are. He conjectured that a sequence with no three
collinear has density zero, and asked whether f₃(n)/3^n → 0, where f₃(n) is the largest
number of points of {0,1,2}^n with no three on a line.

**Result.** Both hold. This follows from the density Hales–Jewett theorem for k = 3
(Furstenberg–Katznelson 1991; elementary proof by Polymath 2009/2012); it is a literature
consequence, not a new resolution.

**Argument.** DHJ(3): for every δ > 0, if n is large then every subset of {0,1,2}^n of size
≥ δ3^n contains a combinatorial line, which is a geometric line of three points. So
f₃(n) = o(3^n). For the integer version: if A has upper density δ > 0, pick N with
|A ∩ [0, N)| ≥ δN/2 and n with 3^(n−1) ≤ N < 3^n; then A ∩ [0, 3^n) has ≥ (δ/6)3^n elements,
whose images lie in {0,1,2}^n (higher digits are 0). For infinitely many such n DHJ(3)
gives three collinear images. So A has upper density 0.

**Evidence.** Hand deduction (second reader). Small values f₃(4) = 43, f₃(5) = 124,
f₃(6) = 353 are from Polymath ("Moser's cube problem"), cited from memory, not re-verified.
Lean status `needs-mathlib` (DHJ(3) is not in Mathlib either).

**Review level.** `rechecked` (the deduction; DHJ itself is cited).
**Prior art.** Furstenberg & Katznelson, J. Anal. Math. 57 (1991); D. H. J. Polymath, Ann. of
Math. 175 (2012). 2026-11-01.
