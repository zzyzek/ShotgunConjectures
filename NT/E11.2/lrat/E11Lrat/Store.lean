import OpenProblemsLib.LRAT

/-! # NT-E11.2: the clause store (untrusted data)

Entries 1..45895: the clauses of `data/c171.cnf`; later entries: the additions of
`data/c171.lrat` (CaDiCaL `--lrat --binary=false`, backward-trimmed). Nothing about the data
is trusted: `E11Lrat.F` checks that the first entries are `cnf 171 L`, the step modules check
every later entry by RUP. -/

namespace E11Lrat

open OpenProblemsLib.LRAT

set_option maxHeartbeats 1000000 in
noncomputable def S : T := lratStore% "NT/E11.2/lrat/data/c171.cnf" "NT/E11.2/lrat/data/c171.lrat"

end E11Lrat
