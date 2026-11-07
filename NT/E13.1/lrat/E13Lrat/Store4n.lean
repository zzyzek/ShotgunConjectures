import OpenProblemsLib.LRAT

/-!
# NT-E13.1, m = 4, split on variable 35 ("12 has colour 2"): the clause store (untrusted data)

Entries 1..25288: the clauses of `data/e13m4n.cnf` (`cnf 4 164` followed by the
unit clause [-35] (12 has not colour 2)); entries 25289..225990: the additions of `data/e13m4n.lrat` (CaDiCaL 2.1.3
`--lrat --binary=false`, backward-trimmed by `../trim.py`). How to regenerate: see
`../README.md`. Nothing about the data is trusted: `E13Lrat.F4n` checks in the kernel that the
first 25288 entries are `cnf 4 164 ++ [[71]]`, and the chunk modules check every later entry by RUP.
-/

namespace E13Lrat

open OpenProblemsLib.LRAT

set_option maxHeartbeats 1000000 in
noncomputable def S4n : T := lratStore% "NT/E13.1/lrat/data/e13m4n.cnf" "NT/E13.1/lrat/data/e13m4n.lrat"

end E13Lrat
