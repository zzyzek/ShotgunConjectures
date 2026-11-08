# NT-E11.2: kernel check of the UNSAT certificate for σ(4, 4) ≤ 171

The upper bound of `../E11_2_lrat.lean` rests on these modules (namespace `E11Lrat`):

| module | content |
|---|---|
| `E11Lrat/Cnf.lean` | `Colourable`, `cnf N L` (alo, amo, colour-symmetry breaking, one clause per listed solution tuple), `sat_of_broken`, `not_colourable_of_unsat` (encoding lemma, including soundness of the symmetry breaking, for every list `L` of valid tuples), `chkF_append` |
| `E11Lrat/Tri.lean` | `L`: the 44 526 solution tuples (x, y, z, c) the proof uses, packed in 45 chunks; `L_valid` (each is a solution of x + y + z = w in [1, 171], c < 4) |
| `E11Lrat/Store.lean` | `S`: clause store read from `data/c171.cnf` and `data/c171.lrat` (untrusted) |
| `E11Lrat/F.lean` | `cnf_length`, `store_cnf` (first 45 895 entries = `cnf 171 L`, checked in 46 chunks), `store_last` |
| `E11Lrat/Q00..Q10.lean` | theorems `steps S n k = true` (at most 8000 hints each, 400 000 per module) |
| `E11Lrat/Steps.lean` | `stepsAll : steps S 45896 187512 = true`, joined by `steps_join` |

`mkmods.py` writes `Tri`, `Store`, `F` from the data; `gen.py Q` writes `Q00..Q10` and `Steps`; `build.sh` compiles
modules to `lib/build/E11Lrat/` (one machine-wide slot, 6 GB, 900 s per module). Compiling a module is its kernel
check. Then `tools/leancheck-mathlib.sh NT/E11.2/E11_2_lrat.lean` checks the final theorems.

Why a sub-CNF: when this proof was built, the store packing of `OpenProblemsLib.LRAT` needed clause ids below 2^18
(the limit is gone since 2026-11-07, see `lib/docs/lrat.md`; the sub-CNF proof is kept). The full CNF has 561 765
clauses, so the proof is rerun on the clauses of its unsat core (all alo/amo/symmetry clauses plus 44 526 triple
clauses). Any list of genuine solution tuples gives a CNF that every symmetry-broken colouring satisfies
(`sat_of_broken`), so unsatisfiability of the sub-CNF is enough.

## Data (not in git)

```bash
cd NT/E11.2/lrat && mkdir -p data
python3 ../certificate/gen2.py 171 > data/f171.cnf                       # full CNF, p cnf 684 561765
cadical --lrat --binary=false data/f171.cnf data/f171.lrat              # CaDiCaL 2.1.3, ~30 s
python3 ../certificate/core.py 561765 data/f171.lrat data/core171.txt   # core: 45 185 clauses
python3 ../certificate/select_core.py 171 data/core171.txt > data/tri171.txt
python3 ../certificate/gen2.py 171 data/tri171.txt > data/c171.cnf     # p cnf 684 45895
cadical --lrat --binary=false data/c171.cnf data/c171.raw.lrat          # ~10 s
python3 ../../E13.1/lrat/trim.py 45895 data/c171.raw.lrat data/c171.lrat # kept 187512, 4 259 759 hints
sha256sum data/c171.cnf data/c171.lrat data/tri171.txt
#   0fde45edc51acbf6cb88c87c7b9c8f1076245d0185465fb4a7e889375f781aa2  data/c171.cnf   (0.9 MB)
#   ada32e7c336567dc132c1d6cd8f65191314378411f4f9cbe5a0cc48334c07e95  data/c171.lrat  (35 MB)
#   941cc94e0330382da6965115822bef6f637c198067b7fc7b4300528a9a3cd478  data/tri171.txt
python3 mkmods.py ; python3 gen.py Q
./build.sh Cnf Tri Store F
./build.sh Q00 Q01 Q02 Q03 Q04 Q05 ; ./build.sh Q06 Q07 Q08 Q09 Q10    # two shells
./build.sh Steps
```

Re-checked 2026-11-07 from scratch after the store packing change of `OpenProblemsLib.LRAT`: `Store` 43 s (needs
`set_option maxHeartbeats 1000000` for elaboration), `F` 73 s, `Q00..Q29` 5142 s (160 to 231 s each, peak 2.5 GB);
`E11_2_lrat.lean` OK, axioms within propext, Classical.choice, Quot.sound.
