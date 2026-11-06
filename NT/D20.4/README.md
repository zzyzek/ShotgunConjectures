# Guy D20: a lattice 7-cluster exists

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D20 (six general points at rational distances). Paraphrased: Noll and Bell found many 6-clusters (lattice points, no three collinear, no four concyclic, all distances integral); is there a 7-cluster?

**Result.** Yes. The seven lattice points
(0, 0), (374400, −2230800), (1081600, −1488240), (−453024, −1630200), (426725, −1630200), (569088, −1291680), (−439040, −1308720)
have all 21 mutual distances integral (largest 2262000), no three on a line and no four on a circle. This is the smallest 7-cluster (by diameter) of Kurz, Noll, Rathbun and Simmons (2014).

**Argument.** Direct computation: each squared distance is a perfect square (the distance table is in the Lean file), each of the 35 triples has nonzero cross product, and each of the 35 quadruples has nonzero determinant det[x²+y², x, y, 1]. If four points satisfied A(x²+y²)+Dx+Ey+F = 0 with A ≠ 0, the Cramer identity A·det = 0 would force det = 0.

**Evidence.**
- Lean (core): [`D20_4.lean`](D20_4.lean), main theorem `D20_4_main` (distinct points, integral distances, no three collinear, no four on a circle A(x²+y²)+Dx+Ey+F = 0 with integer coefficients, A ≠ 0). Axioms propext, Classical.choice, Quot.sound. Outside Lean: that every circle through four lattice points has an equation with integer coefficients (its centre is rational).
- `certificate/check_7cluster.py`: the same checks in Python.

**Review level.** `lean-proof` (modulo the integer-equation remark above).

**Prior art.** Known. S. Kurz, L. C. Noll, R. Rathbun, C. Simmons, Constructing 7-clusters, Serdica J. Computing 8 (2014) 47–70, [arXiv:1312.2318](https://arxiv.org/abs/1312.2318): first 7-clusters by Simmons and Noll (2006), over 1000 found, smallest diameter 2262000; 8-clusters open. Earlier Kreisel–Kurz heptagons (DCG 39, 2008) are not on Z² (coordinates involve √2002). Searched web, arXiv, formal-conjectures (no entry found), 2026-11-06.
