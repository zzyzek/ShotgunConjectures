import OpenProblemsLib.LRAT

/-!
# NT-E29.1: the clause store (untrusted data)

Entries 1..16378: the clauses of `data/e29.cnf`; entries 16379..143080: the additions of
`data/e29.lrat` (CaDiCaL 2.1.3, `--lrat --binary=false`). How to regenerate: see `../README.md`.
Nothing about the data is trusted: `E29Lrat.F` checks in the kernel that the first 16378
entries are `cnf 3150`, and the chunk modules check every later entry by RUP.
-/

namespace E29Lrat

open OpenProblemsLib.LRAT

noncomputable def S : T := lratStore% "NT/E29.1/lrat/data/e29.cnf" "NT/E29.1/lrat/data/e29.lrat"

end E29Lrat
