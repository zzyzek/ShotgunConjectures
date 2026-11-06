# CFG A12: Fickett's cosecant bound for congruent triangles is false

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section A12 (Overlapping convex bodies), after J. W. Fickett, Amer. Math. Monthly 87 (1980) 814-815.
For overlapping congruent convex sets K, K' with boundaries C, C', consider
L1/L2 = length(C ∩ K') / length(C' ∩ K). For congruent triangles with least angle psi the book asks
whether the maximum is cosec(psi/2) (the formula is garbled in our copy; the form
sin(psi/2) <= L1/L2 <= 1/sin(psi/2) is the one quoted by Rasskazova 2012 from the book and
Fickett).

**Result.** No. K = triangle (-5,0), (5,0), (0,12) (sides 10, 13, 13, least angle psi at the apex,
sin(psi/2) = 5/13, psi ≈ 45.24°) and K' = K rotated by (cos, sin) = (-5/13, -12/13) and translated by
(-3.1, 4.6) give L1 = 687563/26910 ≈ 25.551, L2 = 2363/414 ≈ 5.708, L1/L2 ≈ 4.476 > 13/5 = 1/sin(psi/2).
This agrees with N. V. Rasskazova (2012), who states that the bound fails for isosceles triangles
with apex angle psi in (2 arcsin(1/4), pi/3) and proves the sharp-looking bound
Q = 3 + 4 sin(psi/2) there (Q = 4.538 for psi here; our hill climbing reaches 4.532).

**Argument.** All coordinates are rational and all side directions have rational length, so the
part of each side inside the other triangle is a rational fraction of the side (clip the segment
against the three half-planes). Summing gives the exact values above.

**Evidence.**
- Lean (core): [`A12_2.lean`](A12_2.lean). Main theorem `fickett_triangle_counterexample`:
  13/5 < Lsum K K' / Lsum K' K, with `rotation_ok`, `orient_pos`, `sides_K`, `sides_K'`
  (K' congruent to K, side lengths 10, 13, 13), `L1_val`, `L2_val`. Axioms propext,
  Classical.choice, Quot.sound; `decide +kernel`, no `native_decide`.
- [`certificate/exact.py`](certificate/exact.py): the same computation with Python fractions;
  [`certificate/fick.py`](certificate/fick.py): the hill climbing that found the position.
- Outside Lean: that segment clipping by the three half-planes gives the length of the side inside
  the other triangle (standard), and the identification of the least angle (apex, opposite the
  shortest side) with sin(psi/2) = 5/13.

**Review level.** `lean-witness`.

**Prior art.** Known. N. V. Rasskazova, "J. W. Fickett's problem for isosceles triangles",
Vladikavkaz. Mat. Zh. 14(3) (2012) 74-86 (https://www.mathnet.ru/eng/vmj429): remark after (1)
says the conjecture fails for isosceles triangles with 2 arcsin(1/4) < psi < pi/3 (configurations
whose intersection is a quadrilateral); no explicit numbers given there. Equilateral case
1/2 <= L1/L2 <= 2 proved earlier (her reference [4]). Checked 2026-11-06; not in
google-deepmind/formal-conjectures (grep "Fickett").
