import OpenProblemsLib.LRAT

/-!
# NT-E13.1, m = 4, unsplit: the clause store (untrusted data)

Entries 1..25287: the clauses of `data/e13m4.cnf` (`cnf 4 164`); entries 25288..298598: the
additions of `data/e13m4.lrat` (CaDiCaL 2.1.3 `--lrat --binary=false`, backward-trimmed by
`../trim.py`). Ids go beyond 2^18: this store needs the per-entry digit width of
`OpenProblemsLib.LRAT.unpack`. How to regenerate: see `../README.md`. Nothing about the data is
trusted: `E13Lrat.F4` checks in the kernel that the first 25287 entries are `cnf 4 164`, and the
chunk modules check every later entry by RUP.
-/

namespace E13Lrat

open OpenProblemsLib.LRAT

set_option maxHeartbeats 1000000 in
noncomputable def S4 : T := lratStore% "NT/E13.1/lrat/data/e13m4.cnf" "NT/E13.1/lrat/data/e13m4.lrat"

end E13Lrat
