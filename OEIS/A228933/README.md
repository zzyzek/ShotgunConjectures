# OEIS A228933: the optimal ascending continued fraction of 1/φ follows a(n) = a(n-1)^2 - 2 from the fourth term

**Source.** OEIS [A228933](https://oeis.org/A228933): optimal ascending continued fraction
(A228929) of φ - 1 = 1/φ: 2, 4, -18, 322, ... Conjecture (Artico, 2013): "The golden ratio (phi)
expansion exhibits from the fourth term the recurrence relation a(n) = a(n-1)^2 - 2 described in
A228931." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Same lemma as OEIS-A228931 (if |z_k| = 1/U, U > 2 a unit of norm +1, then every later
step squares U and the terms satisfy t ↦ t^2 - 2). For x = 1/φ: r_0 = round(φ) = 2, a(1) = 2,
z_1 = 2/φ - 1 = φ^(-3). r_1 = round(φ^3) = 4 because φ^3 - φ^(-3) = L_3 = 4 (φ^3 has norm -1),
a(2) = 4, z_2 = 4φ^(-3) - 1 = (φ^3 - φ^(-3))φ^(-3) - 1 = -φ^(-6). With U = φ^6 = 9 + 4√5 (norm +1,
U + 1/U = L_6 = 18): a(3) = -18, and from there a(n) = a(n-1)^2 - 2 (a(4) = 322, ...).

**Evidence.**
- `certificate/a228931_check.py` (scan): exact Q(√5) run reproduces the terms (re-run).
- Lean (Mathlib): [`A228933_mathlib.lean`](A228933_mathlib.lean), `A228933_main`: with the A228929 algorithm defined over ℝ (Mathlib `round`) and x = 1/φ: a(1) = 2, a(2) = 4, a(3) = -18, a(4) = 322, a(n) > 0 and a(n) = a(n-1)^2 - 2 for every n >= 4. Outside Lean: none.

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Prior art.** Partly known. [OEIS A228933](https://oeis.org/A228933) (fetched 2026-11-04) still states the conjecture. The key lemma is in [G. Artico's proof for A228931](https://oeis.org/A228931/a228931.pdf); its application to 1/phi (first remainders, unit phi^6) is not written there. Searched: entry, OEIS cross-reference search, edit history, Artico pdf. Worth a short OEIS comment. (Prior-art review 2026-11-04.)
