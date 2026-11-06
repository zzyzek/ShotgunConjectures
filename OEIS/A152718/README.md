# OEIS A152718: inverse Motzkin transform of A054393

**Source.** [A152718](https://oeis.org/A152718) (offset 0), R. J. Mathar, Dec 11 2008: a(n) = 2a(n-1) - a(n-2) +
2a(n-3) - a(n-4) + a(n-5) for n > 5, with a(0..5) = 1, 1, 1, 1, 2, 4. Comment: "Conjecture: this is the inverse
Motzkin transform of A054393." G.f. 1 + x(-1 + x + x^3)/(-1 + 2x - x^2 + 2x^3 - x^4 + x^5) (Mathar, 2016).
[A054393](https://oeis.org/A054393) (Sloane and Pergola, 2000) counts permutations with certain forbidden
subsequences (Barcucci et al., "From Motzkin to Catalan permutations", Discrete Math. 217 (2000) 33-49); its
Mathematica program (Alcover, 2018) gives a(n) = (M^n)[1,1] for the n x n 0/1 matrix with M[i,j] = 1 iff j < i,
or i = j <= 5, or j = i+1. (OEIS text, CC BY-SA 4.0, revisions #21 of A152718 and #29 of A054393, checked
2026-11-06.)

**Reading.** Mathar uses "inverse Motzkin transform" for the substitution x -> x/(1+x+x^2) in the g.f. (see his
comments in A097861, A109196, A147691); equivalently A054393(x) = A152718(z) with z = x M(x), M the Motzkin
series, so z = x(1 + z + z^2). In coefficients: A054393(n) = sum_{k=0..n} A152718(k) [x^n] z^k. The matrix power
counts walks of length n on levels 1, 2, ... from level 1 back to level 1; a step goes up one level, drops to any
lower level, or stays put, staying only at levels 1..5 (levels 0..4 below). A walk of length n never goes above
level n/2 + 1, so the n x n truncation loses nothing.

**Result.** True: A054393(x) = A152718(x M(x)) as formal power series, so A152718 is the inverse Motzkin transform
of A054393.

**Argument.** Number the levels 0, 1, 2, ... and let E_h(x) count excursions at level h (walks from h back to h
that never go below h), G_h(x) count walks from h staying at or above h and ending anywhere.

1. *Decomposition.* An excursion at h is a sequence of loops at h (allowed iff h <= 4) and of arches: an up step to
   h+1, a walk counted by G_{h+1}, and one drop back to h. So E_h = 1/(1 - [h <= 4] x - x^2 G_{h+1}). Cutting a walk
   from h at its last visit to h gives G_h = E_h (1 + x G_{h+1}).
2. *Top levels.* For h >= 5 there are no loops, so E_h = E, G_h = G for all h >= 5. With no loops at all levels but
   one loop allowed at the base, the excursion series is the Motzkin series: 1/(1 - x - x^2 G) = M, which gives
   x^2 G = 1 - x - 1/M = x^2 M (from M = 1 + xM + x^2 M^2), i.e. G = M = z/x.
3. *Levels 4..0.* With x = z/(1+z+z^2): E_4 = 1/(1 - x - x^2 M) = M = 1+z+z^2, G_4 = M(1+z);
   E_3 = 1/(1-z); E_2 = (1-z)(1+z+z^2)/(1-z-z^3); E_1 = (1-z-z^3)/(1-2z+z^2-z^3); and
   E_0 = (1+z+z^2)(1-2z+z^2-z^3)/(1-2z+z^2-2z^3+z^4-z^5) = (1-z-2z^3-z^5)/(1-2z+z^2-2z^3+z^4-z^5).
4. *Comparison.* The last expression is Mathar's g.f. of A152718 evaluated at z, and E_0 is the g.f. of A054393.

The Lean proof runs the argument backwards, which avoids infinite sums of series: it defines candidate series
V_j (walks from 0 ending at level j: V_j = X^j U_j with U_j explicit rational expressions in z, and
U_{j+1}/U_j = (1+z+z^2)/(1+z) for j >= 4) and tails T_j (= sum_{i>j} V_i), checks that they satisfy the
dynamic-programming equations of the walk count (polynomial identities in z, u^{-1}, (1+z)^{-1}, Q(z)^{-1} with
explicit cofactors), and concludes by induction on the length that their coefficients are the walk counts.

**Evidence.**
- Lean (Mathlib): [`A152718_mathlib.lean`](A152718_mathlib.lean). Definitions: `w n j` (walks of length n from
  level 0 to level j, by the length recursion w(n+1, j) = w(n, j-1) + [j <= 4] w(n, j) + sum_{j < i <= n} w(n, i)),
  `A054393 n = w n 0`, `A152718` (the recurrence), `mot`/`zM` (z = sum mot(n) x^n, `zM_eq : zM = X * (1 + zM +
  zM^2)`). Main theorems: `A152718_motzkin : mk A054393 = (mk A152718).subst zM` and `A152718_motzkin_coeff :
  A054393 n = sum_{k in range (n+1)} A152718 k * coeff n (zM^k)`. Route: `algE0`..`algE5`, `algT`, `core1`, `core2`
  (ring identities with `linear_combination` cofactors from certificate/cofactors.py), `D0`, `D1`, `D2`, `DT`
  (walk-count equations for the series), `T_tele`, `coeff_T`, `coeff_V` (uniqueness by induction), `gfB` (g.f. of
  the recurrence), `subst_eq`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms of every theorem at
  most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): the walk recursion equals Alcover's matrix power for n <= 40,
  the A054393 b-file (n = 0..26) and the A152718 b-file (n <= 150); the transform identity holds for n <= 150;
  mot(n+1) is the Motzkin number.
- [`certificate/derive.py`](certificate/derive.py): sympy check of steps 1-4.
- [`certificate/cofactors.py`](certificate/cofactors.py): produces the `linear_combination` cofactors.
- Outside Lean: that the walk recursion `w` is the OEIS definition of A054393 (the matrix power, and the
  permutation class of Barcucci et al.). certificate/check.py compares it with the matrix power for n <= 40 and
  with the 27 b-file terms; the permutation interpretation is taken from the entry.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The A152718 entry and history keep the statement as a conjecture; A054391 and
A054394 carry analogous unproved comments by Mathar. Not in google-deepmind/formal-conjectures (no
`FormalConjectures/OEIS/152718.lean`) or otoi-lab/oeis-lean-proofs. A web search found no statement of the
transform. Barcucci et al. (2000) derive the counting for this family through a succession rule; their paper was
not read (paywalled), so whether it gives the g.f. in a form that makes the conjecture immediate is open.
