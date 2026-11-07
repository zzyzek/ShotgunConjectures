# Guy UPINT E13: values of Turán's s(m, n)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section E13 (paraphrased): s(m, n) is the
least s such that every partition of [m, m + s] into n classes has a class containing a solution of x + y = z
(x = y allowed). Turán: s(m, 2) = 4m. Clearly s(1, n) is the Schur number S(n). Abbott and Znám:
s(m, n) ≥ 3 s(m, n-1) + m. Guy lists only bounds for n ≥ 3.

**Result.**
1. s(m, 3) = 13m for every m ≥ 1.
2. Computation: s(m, 4) = 44, 82, 120, 160 for m = 1, 2, 3, 4 (lower bound 40m, upper bound 44m from
   item 1's argument).

**Argument.** Lower bound: the Abbott-Znám step. Turán's colouring of [m, 5m-1] (class A = [m, 2m) ∪ [4m, 5m),
class B = [2m, 4m)) is sum-free; colour [5m, 10m) with a new class C (its smallest sum is 10m) and [10m, 14m) by
shifting Turán's colouring up by 9m. A sum x + y = z inside one old class with x < 5m ≤ y would map to x + (y - 9m)
= z - 9m inside Turán's colouring, and two elements ≥ 10m sum beyond 14m. So [m, 14m - 1] is 3-colourable.
Upper bound: [m, 14m] contains m, 2m, ..., 14m, a copy of [1, 14] scaled by m, and Schur's S(3) = 13
(Baumert 1965) says every 3-colouring of [1, 14] has a monochromatic x + y = z. The same scaling gives
s(m, n) ≤ m·S(n) in general, which for n = 3 meets the Abbott-Znám bound 3·4m + m.
For n = 4 the two bounds are 40m and 44m; SAT (CaDiCaL via pysat) gives 44, 82, 120, 160, so s(m, 4) = 40m for
m = 3, 4. For m = 5 the solver did not decide s = 200 within 30 minutes (one core).

**Evidence.**
- Lean (core): [`E13_1.lean`](E13_1.lean), namespace `NT_E13_1`. Main theorem `s_m_3`: with `Colourable m s n`
  = "[m, m + s] has an n-colouring without monochromatic x + y = z", Colourable m (13m - 1) 3 and
  ¬ Colourable m (13m) 3 for every m ≥ 1. `schur3` (S(3) ≤ 13) is a backtracking search evaluated by the kernel
  (`search14`, `decide`) plus its soundness proof `sound`; `colouring3_sumfree` checks the colouring for all m by
  `omega`. Check: `tools/leancheck.sh`, exit 0, no warnings; axioms propext, Quot.sound.
- [`certificate/smn.py`](certificate/smn.py): SAT computation of s(m, 2) (= 4m, m ≤ 6, a check of the encoding),
  s(m, 3) (= 13m, m ≤ 8) and s(m, 4) (m ≤ 4); `smn_range.py` for larger m.
- Outside Lean: the s(m, 4) values (SAT, no DRAT proof kept).

**Review level.** `lean-proof` for s(m, 3) = 13m; `agent` for the s(m, 4) values.

**Prior art.** Checked 2026-11-06: Guy E13 lists s(m, 2) = 4m and bounds; web search found no statement of
s(m, 3) = 13m, though both halves are immediate from known facts (Abbott-Znám, Schur S(3) = 13). Not in
google-deepmind/formal-conjectures (clone 2026-11-06; Schur-type files concern intervals starting at 1).
