# OEIS A110320: blocks in RNA secondary structures via Whitney numbers

**Source.** [A110320](https://oeis.org/A110320) (number of blocks in all RNA secondary structures with n nodes),
formula by G. McGarvey (2007): "Conjecture: a(n) = (A051292(n+2)-A051286(n+1))/2." (OEIS text, CC BY-SA 4.0.)

**Result.** True, given the printed g.f.s: A110320 (E. Deutsch), A051286 = 1/R, A051292 = (1 − z² + R)/R with
R = √(1 − 2z − z² − 2z³ + z⁴).

**Argument.** With these g.f.s the difference between Deutsch's g.f. (1−z−z²)/(2z²R) − 1/(2z²) and
Σ_{n≥1} ½(A051292(n+2) − A051286(n+1)) z^n simplifies to 0: the parts with 1/R give
((1 − z²) − z)/(2z²R), and the polynomial parts cancel.

**Evidence.**
- `certificate/gf_check.py` (scan script): sympy simplification of the g.f. difference to 0.
- `certificate/check.py`: independent of the printed g.f.s, computes all three sequences from their definitions
  (RNA structures by dynamic programming; order ideals of the fence and the crown by transfer matrices) and checks
  the identity for n ≤ 40.
- Lean (Mathlib): [`A110320_mathlib.lean`](A110320_mathlib.lean), theorem `A110320_gf_identity`: with the three
  sequences defined as coefficients of the printed g.f.s in `ℚ⟦X⟧` (for any R with constant coefficient 1, in
  particular R = √(1 − 2z − z² − 2z³ + z⁴)), a(n) = (A051292(n+2) − A051286(n+1))/2. Outside Lean: that the
  printed g.f.s generate the combinatorial sequences (`certificate/check.py`, n ≤ 40).

**Review level.** `lean-witness`.
**Prior art.** Verdict partly-known, immediate (OEIS status conjecture; searched 2026-11-04). With Tenn's crown = fence(n) - fence(n-2) identity, McGarvey's conjecture is Irwin's formula rewritten; nobody has written that down. Sources: [OEIS A110320 (fetched 2026-11-04)](https://oeis.org/A110320): McGarvey 2007 formula still labelled Conjecture; Irwin 2016 formula a(n)=(A051286(n+2)-A051286(n+1)-A051286(n))/2 listed; [M. Tenn, Lattice walks, pattern statistics, and Riordan arrays, arXiv:2607.29612 (Jul 2026)](https://arxiv.org/abs/2607.29612): Prop. 4.1.12: crown ideals = g(n,k) - g(n-2,k), i.e. A051292(n) = A051286(n) - A051286(n-2); Remark 4.1.13 says this 'appears relevant' to the A110320 conjecture but does not prove it; [OEIS A051292 (fetched 2026-11-04)](https://oeis.org/A051292): Munarini-Salvi g.f. for the crown Whitney numbers. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A051286, A051292, A125250; Google/arXiv: RNA blocks Whitney numbers fence crown.
