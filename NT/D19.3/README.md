# Guy D19 (Evans): every attainable integer ratio base/height occurs for infinitely many primitive triangles

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D19 (Evans's remarks after Bergum's problem). Paraphrased: which integers n occur as base/height of an integer-sided triangle, and (dually) as height/base? If a ratio can occur, are there infinitely many primitive triangles for which it occurs?

**Reading.** Evans's ratios are integers n (base/height) or 1/n (height/base = n). Triangles may be acute or obtuse (Guy's sign of n).

**Result.** Yes, for every ratio r = base/height with r² + 4 not a rational square, in particular for every integer ratio n and every 1/n. For rational ratios the answer can be no: base/height = 3/2 is attained only by the triangle (5, 5, 6) up to similarity.

**Argument.** Put the base on the x-axis, height 1, apex (u, 1); the sides √(u²+1), √((r−u)²+1) are rational iff u = (s − 1/s)/2 and r − u = (t − 1/t)/2 with s, t ∈ Q×. So triangles of ratio r correspond to rational points of the cubic C_r: (s + t)(st − 1) = 2r·st with s, t ∉ {0, ∞}; each shape gives at most 8 points. C_r always has 4 trivial points: (0, 0) and the three points at infinity. C_r is isomorphic (PARI `ellfromeqn`) to E_r: y² = x(x² + (r² + 2)x + 1), discriminant 16r²(r² + 4), whose rational torsion contains Z/4 = {O, (0,0), (−1, ±r)} (these are the trivial points).
- No other 2-torsion: x² + (r²+2)x + 1 has discriminant r²(r²+4), not a square by assumption (for r = n or 1/n, r² + 4 = □ forces n = 0).
- No point of order 8: 2P = (−1, ±r) means x(2P) = (x²−1)²/(4x(x²+Ax+1)) = −1, i.e. (x + 1/x)² + 4(x + 1/x) + 4r² + 4 = 0, whose discriminant is −16r² < 0.
- No point of order 3: on the 3-division curve 3x⁴ + 4Ax³ + 6x² − 1 = 0 one gets r² = −(x+1)³(3x−1)/(4x³) and y² = (x²−1)²/(4x), so x = s² and w² = (1 − 3s²)(1 + s²). This quartic is an elliptic curve of conductor 48 with rank 0 (2-descent upper bound 0) and torsion Z/2, so its only rational points are (0, ±1), giving x = 0, which is not on the division curve.
By Mazur's theorem the torsion groups containing Z/4 are Z/4, Z/8, Z/12, Z/2×Z/4, Z/2×Z/8; all but Z/4 are excluded. So E_r(Q)_tors = Z/4 consists of the trivial points, and any triangle gives a point of infinite order, hence infinitely many rational points, hence infinitely many shapes, each scaling to one primitive integer triangle.
For r = 3/2 (r² + 4 = 25/4) the torsion is Z/2×Z/4 and the rank is 0 (2-descent upper bound 0). The 4 nontrivial points (2, 2), (2, −1/2), (−1/2, 2), (−1/2, −1/2) all give u = 3/4: the triangle 5, 5, 6. Likewise r = 8/3 gives only (5, 5, 8).

**Evidence.**
- `certificate/ranks.gp` (`ranks.out`): torsion Z/4 for r = n, 1/n, n ≤ 40; rank bounds (e.g. ratios 1, 2 and height/base 2 give rank 0: no triangle; 1/3, 5, 8, 1/8, 42 give rank ≥ 1, matching Guy's examples).
- `certificate/aux.gp`: the order-3 auxiliary curve has rank [0, 0] and torsion Z/2; the family r = (k² − 4)/(2k) has torsion Z/2×Z/4.
- `certificate/ratio3over2.gp` (`.out`): r = 3/2 has torsion Z/2×Z/4, rank 0, and the four listed points lie on C_r.
- Lean: none. Outside Lean: everything; it needs Mazur's torsion theorem and a 2-descent, neither in Mathlib.

**Review level.** `rechecked` (torsion argument re-derived by hand; ranks by PARI `ellrank`, whose upper bound is unconditional).

**Prior art.** Partly known. A. J. MacLeod, *Elliptic curves in recreational number theory*, [arXiv:1610.03430](https://arxiv.org/abs/1610.03430), §4.3, derives the same curve y² = x³ + (N²+2)x² + x for integer N, shows its torsion is Z/4 with all torsion points degenerate, and concludes a triangle needs rank ≥ 1; the step to "infinitely many primitive triangles" (Evans's question) is immediate but not stated there. The 1/n case and the rational-ratio counterexample 3/2 are not in that source. Searched web, arXiv, formal-conjectures (no entry), 2026-11-06.
