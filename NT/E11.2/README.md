# Guy UPINT E11: the generalized Schur number σ(4, 4) = 171 (partial)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section E11 (paraphrased): σ(m, n) is the
least v such that every n-colouring of [1, v] has a monochromatic solution of a₁ + … + a_{m−1} = a_m (the a_i not
necessarily distinct); σ(m, 2) = m² − m − 1, and the problem asks for the values in general.

**Result (partial; the general problem stays open).** σ(4, 4) = 171 = 4⁴ − 4³ − 4² − 4 − 1, i.e. [1, 170] has a
4-colouring with no monochromatic x + y + z = w and every 4-colouring of [1, 171] has one.

**Argument.**
- Lower bound: an explicit colouring of [1, 170] (found by CaDiCaL; it has the block shape of the recursive
  Ahmed–Schaal construction: 00 111111 00 2…2 00 111111 00 3…3 …), checked over all solutions with w ≤ 170.
- Upper bound: the CNF "4-colouring of [1, 171] with no monochromatic x + y + z = w" with colour-symmetry breaking
  (1 has colour 0; 3 has colour 1, which is sound because 1 + 1 + 1 = 3; colour 3 appears only after colour 2) is
  unsatisfiable (CaDiCaL 2.1.3, 31 s). The breaking is sound because any valid colouring can be renamed: send the
  colours of 1 and 3 to 0 and 1, the first other colour to appear to 2, the last to 3. For the kernel check the
  proof is rerun on the clauses of its unsat core (all every-number-has-a-colour, at-most-one-colour and symmetry
  clauses, plus 44 526 of the 560 396 solution clauses); a sub-CNF of genuine constraints being unsatisfiable is
  enough.

**Evidence.**
- Lean: [`E11_2_lrat.lean`](E11_2_lrat.lean), main theorem `sigma4_4 : sigma4 4 = 171` (`sigma4 n` = least N with
  `¬ Colourable N n`, `IsSigma`), with `lower` (explicit colouring `col170`, `decide`) and `upper`
  (`not_colourable_of_unsat` from `lrat/E11Lrat/Cnf.lean`, which proves the encoding and the symmetry breaking
  sound for any list of valid solution tuples, plus `unsat_of_parts` from `OpenProblemsLib.LRAT`: 187 512 RUP
  additions, 4.26M hints, checked in 30 modules `lrat/E11Lrat/Q00..Q29`). Build: `lrat/README.md`; then
  `tools/leancheck-mathlib.sh NT/E11.2/E11_2_lrat.lean`. Axioms propext, Classical.choice, Quot.sound.
  The LRAT data (35 MB) are not in git; `lrat/README.md` has the regeneration steps and sha256 sums.
- Scripts: `certificate/gen2.py` (CNF in Lean clause order), `certificate/core.py` (trim + unsat core),
  `certificate/select_core.py`, `certificate/gen_cnf_check.py` (independent encoding used to reproduce
  σ(3,3) = 14, σ(3,4) = S(4)+1 = 45, σ(4,3) = 43 and the 170/171 threshold).
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: Guy E11; Ahmed–Schaal, *On generalized Schur numbers* (2016, table of all
known values: 4-colour values only for x + y = z type rows S(4; 3,3,3,t)); Boza–Marín–Revuelta–Sanz (2019) for
3 colours; Chang–De Loera–Wesley (2022) and arXiv:2604.11030 abstracts; web searches for "S(4,4)" with 171. No
4-colour value for m ≥ 4 found, so σ(4, 4) = 171 appears new. It matches the general lower bound
σ(m, n) ≥ m^n − m^{n−1} − … − m − 1. Not in google-deepmind/formal-conjectures (clone of 2026-11-06).
