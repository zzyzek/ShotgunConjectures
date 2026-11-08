import E13Lrat.F4
import E13Lrat.Steps4

/-! # NT-E13.1, m = 4: `cnf 4 164` is unsatisfiable from one store of 298 598 entries (unsplit)

A demonstration that `OpenProblemsLib.LRAT` handles clause ids beyond 2^18: the same statement as
`cnf4_unsat` in `../../E13_1_lrat.lean`, which is proved there from the split on variable 35. -/

namespace E13Lrat

open OpenProblemsLib.LRAT

theorem cnf4_unsat_unsplit : Unsat (cnf 4 164) :=
  unsat_of_parts (cnf 4 164) S4 25287 273311 cnf4_length store4_cnf (by decide) steps4 store4_last

end E13Lrat
