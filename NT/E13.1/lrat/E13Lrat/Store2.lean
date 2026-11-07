import OpenProblemsLib.LRAT

/-!
# NT-E13.1, m = 2: the clause store (untrusted data)

Entries 1..6891: the clauses of `data/e13m2.cnf`; entries 6892..241503: the additions of
`data/e13m2.lrat` (CaDiCaL 2.1.3 `--lrat --binary=false`, backward-trimmed by `../trim.py`).
How to regenerate: see `../README.md`. Nothing about the data is trusted: `E13Lrat.F2` checks
in the kernel that the first 6891 entries are `cnf 2 84`, and the chunk modules check every
later entry by RUP.
-/

namespace E13Lrat

open OpenProblemsLib.LRAT

noncomputable def S2 : T := lratStore% "NT/E13.1/lrat/data/e13m2.cnf" "NT/E13.1/lrat/data/e13m2.lrat"

end E13Lrat
