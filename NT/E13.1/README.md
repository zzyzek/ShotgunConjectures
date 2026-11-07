# Guy UPINT E13: values of Turán's s(m, n)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section E13 (paraphrased): s(m, n) is the
least s such that every partition of [m, m + s] into n classes has a class containing a solution of x + y = z
(x = y allowed). Turán: s(m, 2) = 4m. Clearly s(1, n) is the Schur number S(n). Abbott and Znám:
s(m, n) ≥ 3 s(m, n-1) + m. Guy lists only bounds for n ≥ 3.

**Result.**
1. s(m, 3) = 13m for every m ≥ 1.
2. s(2, 4) = 82 and s(4, 4) = 160, proved in Lean (kernel-checked LRAT certificates); s(m, 4) ≥ 40m
   for every m ≥ 1, proved in Lean.
3. Computation: s(1, 4) = 44 (Schur S(4)) and s(3, 4) = 120 (SAT, no kept proof); bounds 40m ≤ s(m, 4) ≤ 44m
   from item 1's argument.

**Argument.** Lower bound: the Abbott-Znám step. Turán's colouring of [m, 5m-1] (class A = [m, 2m) ∪ [4m, 5m),
class B = [2m, 4m)) is sum-free; colour [5m, 10m) with a new class C (its smallest sum is 10m) and [10m, 14m) by
shifting Turán's colouring up by 9m. A sum x + y = z inside one old class with x < 5m ≤ y would map to x + (y - 9m)
= z - 9m inside Turán's colouring, and two elements ≥ 10m sum beyond 14m. So [m, 14m - 1] is 3-colourable.
Upper bound: [m, 14m] contains m, 2m, ..., 14m, a copy of [1, 14] scaled by m, and Schur's S(3) = 13
(Baumert 1965) says every 3-colouring of [1, 14] has a monochromatic x + y = z. The same scaling gives
s(m, n) ≤ m·S(n) in general, which for n = 3 meets the Abbott-Znám bound 3·4m + m.
For n = 4 the two bounds are 40m and 44m (the Abbott-Znám step once more: the 3-colouring of [m, 14m - 1],
a new class [14m, 28m), and the 3-colouring shifted up by 27m on [28m, 41m - 1]); SAT (CaDiCaL) gives 44, 82, 120,
160, so s(m, 4) = 40m for m = 3, 4. For m = 2 and m = 4 the upper bound is the unsatisfiability of the CNF "[m, m +
s] has a 4-colouring without monochromatic x + y = z" at s = 82 and s = 160, with colour-symmetry breaking (m gets
colour 0, 2m colour 1, colour 3 only after colour 2 has appeared). The breaking is sound because any valid
colouring can be renamed into that form: m and 2m have different colours (m + m = 2m), so send them to 0 and 1,
the first other colour to appear to 2 and the remaining one to 3. The lower bound for m = 2 is an explicit
colouring of [2, 83] found by the solver. For m = 5 the solver did not decide s = 200 within 30 minutes (one core).

**Evidence.**
- Lean (core): [`E13_1.lean`](E13_1.lean), namespace `NT_E13_1`. Main theorem `s_m_3`: with `Colourable m s n`
  = "[m, m + s] has an n-colouring without monochromatic x + y = z", Colourable m (13m - 1) 3 and
  ¬ Colourable m (13m) 3 for every m ≥ 1. `schur3` (S(3) ≤ 13) is a backtracking search evaluated by the kernel
  (`search14`, `decide`) plus its soundness proof `sound`; `colouring3_sumfree` checks the colouring for all m by
  `omega`. Check: `tools/leancheck.sh`, exit 0, no warnings; axioms propext, Quot.sound.
- [`certificate/smn.py`](certificate/smn.py): SAT computation of s(m, 2) (= 4m, m ≤ 6, a check of the encoding),
  s(m, 3) (= 13m, m ≤ 8) and s(m, 4) (m ≤ 4); `smn_range.py` for larger m.
- Lean (LRAT): [`E13_1_lrat.lean`](E13_1_lrat.lean), checked with `tools/leancheck-mathlib.sh` after compiling
  the modules of [`lrat/`](lrat/README.md) with `lrat/build.sh`. Main theorems `s_2_4 : s 2 4 = 82` and
  `s_4_4 : s 4 4 = 160`, where `s m n` is the least s with `¬ Colourable m s n` (`IsS`). Upper bounds:
  `cnf m N` is defined in Lean from the problem (`lrat/E13Lrat/Cnf.lean`); the encoding lemma
  `not_colourable_of_unsat` includes the soundness of the symmetry breaking; unsatisfiability of `cnf 2 84` and
  `cnf 4 164` by kernel-checked LRAT (CaDiCaL 2.1.3, backward-trimmed: 234 612 RUP additions, 4.58M hints, 98 min
  kernel time for m = 2; for m = 4 a case split on "12 has colour 2" (`unsat_of_split`, needed because the store packing allows
  ids below 2^18): 61 221 + 200 702 additions, 5.73M hints, 123 min). Lower bounds: explicit colouring
  `col2_4` (`decide`) and `lower_m_4` (all m, by `omega`). Axioms propext, Classical.choice, Quot.sound; no
  warnings. The LRAT data (89 MB) are not in git; `lrat/README.md` has the regeneration steps and sha256 sums.
- Outside Lean: the values s(1, 4) = 44 and s(3, 4) = 120 (SAT, no proof kept).

**Review level.** `lean-proof` for s(m, 3) = 13m, s(2, 4) = 82, s(4, 4) = 160 and s(m, 4) ≥ 40m; `agent` for
s(3, 4) = 120 (s(1, 4) = 44 is Schur's S(4), Baumert 1965).

**Prior art.** Checked 2026-11-06: Guy E13 lists s(m, 2) = 4m and bounds; web search found no statement of
s(m, 3) = 13m, though both halves are immediate from known facts (Abbott-Znám, Schur S(3) = 13). Not in
google-deepmind/formal-conjectures (clone 2026-11-06; Schur-type files concern intervals starting at 1).
