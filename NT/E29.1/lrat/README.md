# NT-E29.1: kernel check of the UNSAT certificate for [3, 3150]

The upper bound of `../E29_1_lrat.lean` rests on these modules (namespace `E29Lrat`):

| module | content | check |
|---|---|---|
| `E29Lrat/Cnf.lean` | `Forces`, `cnf N` from the problem, `forces_of_unsat` (encoding lemma) | 1 s |
| `E29Lrat/Store.lean` | `S`: clause store read from `data/e29.cnf` and `data/e29.lrat` (untrusted) | 23 s, 1.1 GB |
| `E29Lrat/F.lean` | `cnf_length`, `store_cnf` (first 16378 entries = `cnf 3150`), `store_last` | 23 s, 3.4 GB |
| `E29Lrat/C00..C07.lean` | 375 theorems `steps S n k = true` (at most 8000 hints each) | 477 to 494 s each (C07: 245 s), peak 2.7 to 3.1 GB; 3647 s total |
| `E29Lrat/Steps.lean` | `steps_all : steps S 16379 126702 = true`, joined by `steps_join` | 1 s |

`gen.py` writes `C00..C07` and `Steps` from `data/e29.lrat`; `build.sh` compiles modules to
`lib/build/E29Lrat/` (one machine-wide slot, 6 GB, 900 s per module, as `tools/buildlib.sh`).
Compiling a module is its kernel check. Then `tools/leancheck-mathlib.sh NT/E29.1/E29_1_lrat.lean`
checks the final theorem and prints its axioms (which include everything imported).

## Data (not in git; 24 MB)

```bash
cd NT/E29.1/lrat && mkdir -p data
zcat ../certificate/unsat_3_3150.cnf.gz > data/e29.cnf     # sha256 892fd03c...a2f1
cadical --lrat --binary=false data/e29.cnf data/e29.lrat     # CaDiCaL 2.1.3, 3 s
sha256sum data/e29.lrat   # 89131844b87e051c812abfab6b8d14bab8a99532e006fd1221e2a962b6d1c5ff
python3 gen.py 8000 400000
./build.sh Cnf Store F            # then, in two shells:
./build.sh C00 C01 C02 C03 ; ./build.sh C04 C05 C06 C07
./build.sh Steps
cd ../../.. && tools/leancheck-mathlib.sh NT/E29.1/E29_1_lrat.lean
```

CaDiCaL is deterministic: rerunning it on the same CNF gave the same LRAT file (checked
2026-11-07). The data only feed the store; any LRAT proof of `data/e29.cnf` works.

The `.olean` files depend on `lib/build/OpenProblemsLib/LRAT.olean`: after `tools/buildlib.sh`
rebuilds `LRAT`, rebuild these modules too (all of them, in the order above).

Checked 2026-11-07: all modules built with no warnings; `E29_1_lrat.lean` OK, `forces_iff` axioms
propext, Classical.choice, Quot.sound.
