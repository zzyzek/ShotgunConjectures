# NT-E13.1: kernel check of the UNSAT certificates for s(2, 4) and s(4, 4)

The upper bounds of `../E13_1_lrat.lean` rest on these modules (namespace `E13Lrat`):

| module | content | check |
|---|---|---|
| `E13Lrat/Cnf.lean` | `Colourable`, `cnf m N` from the problem, `not_colourable_of_unsat` (encoding lemma, including soundness of the colour-symmetry breaking) | 3 s |
| `E13Lrat/Store2.lean` | `S2`: clause store read from `data/e13m2.cnf` and `data/e13m2.lrat` (untrusted) | 42 s, 1.4 GB |
| `E13Lrat/F2.lean` | `cnf2_length`, `store2_cnf` (first 6891 entries = `cnf 2 84`), `store2_last` | 10 s, 1.9 GB |
| `E13Lrat/A00..A11.lean` | theorems `steps S2 n k = true` (at most 8000 hints each, 400 000 per module) | 240 to 537 s each, peak 2.4 to 2.7 GB; 5905 s total |
| `E13Lrat/Steps2.lean` | `steps2 : steps S2 6892 234612 = true`, joined by `steps_join` | 2 s |
| `E13Lrat/Store4p.lean`, `Store4n.lean` | `S4p`, `S4n`: stores from `data/e13m4p.*`, `data/e13m4n.*` (m = 4 split on variable 35, "12 has colour 2") | 41 s, 1.4 GB; 11 s, 1.0 GB |
| `E13Lrat/F4p.lean`, `F4n.lean` | first 25288 entries = `cnf 4 164 ++ [[70]]`, resp. `++ [[71]]`; last entries empty | 54 s, 5.5 GB; 48 s, 5.4 GB |
| `E13Lrat/P00..P03.lean`, `N00..N11.lean` | theorems `steps S4p n k = true`, `steps S4n n k = true` (same chunk sizes) | 38 to 507 s each, peak 2.1 to 2.7 GB; 7361 s total |
| `E13Lrat/Steps4p.lean`, `Steps4n.lean` | `steps4p : steps S4p 25289 61221 = true`, `steps4n : steps S4n 25289 200702 = true` | 0 s, 2 s |

`gen.py t P` writes the chunk modules `P00..` and `Steps<t>` from `data/e13m<t>.lrat` (t = 2, 4p, 4n); `build.sh`
compiles modules to `lib/build/E13Lrat/` (one machine-wide slot, 6 GB, 900 s per module, as
`tools/buildlib.sh`). Compiling a module is its kernel check. Then
`tools/leancheck-mathlib.sh NT/E13.1/E13_1_lrat.lean` checks the final theorems and prints their
axioms (which include everything imported).

## The CNF

`cnf m N` (Lean) and `cnf.py m 4 (N - m)` (DIMACS, same clause order) encode "[m, N] has a
4-colouring with no monochromatic x + y = z" with variable `4 (x - m) + c + 1` for "x has colour
c": every x has a colour; for m <= x <= y, x + y <= N and each colour c, not all of x, y, x + y
have colour c; m has colour 0, 2m has colour 1, and colour 3 at i > m needs colour 2 at some
j in [m, i). The encoding lemma recolours any valid colouring into this form (colour of m to 0,
colour of 2m to 1, the first other colour to appear to 2, the last to 3).

## Data (not in git)

```bash
cd NT/E13.1/lrat && mkdir -p data
python3 cnf.py 2 4 82 > data/e13m2.cnf                                  # p cnf 332 6891
cadical --lrat --binary=false data/e13m2.cnf data/e13m2.raw.lrat         # CaDiCaL 2.1.3, ~10 s
python3 trim.py 6891 data/e13m2.raw.lrat data/e13m2.lrat                 # backward trim
sha256sum data/e13m2.cnf data/e13m2.lrat
#   398c0b7896b60740b4cf5405dec1424e25ba1f105a739508e071158f4c1e6c26  data/e13m2.cnf   (119 KB)
#   4f850754ba625b35d6e865f9c76b5c7a4a24c8cab522995c756e02e7c8aa6e28  data/e13m2.lrat  (40 MB; 234612 additions, 4577988 hints)
python3 cnf.py 4 4 160 > data/e13m4.cnf                                 # p cnf 644 25287
# m = 4 is split on variable 35 ("12 has colour 2"): the store packing of OpenProblemsLib.LRAT
# needed ids below 2^18 when this proof was built, and the unsplit trimmed proof has 273311 additions
# after 25287 clauses. The limit is gone since 2026-11-07 (see "Unsplit m = 4" below).
for t in p n; do s=""; [ $t = n ] && s="-"
  { head -1 data/e13m4.cnf | awk '{print $1,$2,$3,$4+1}'; tail -n +2 data/e13m4.cnf; echo "${s}35 0"; } > data/e13m4$t.cnf
  cadical --lrat --binary=false data/e13m4$t.cnf data/e13m4$t.raw.lrat    # ~20 s each
  python3 trim.py 25288 data/e13m4$t.raw.lrat data/e13m4$t.lrat
done
sha256sum data/e13m4p.cnf data/e13m4p.lrat data/e13m4n.cnf data/e13m4n.lrat
#   c8f293f7ba4500d1e2a1c830f887907ef8d980b67eabe7160ac7d7602f09145d  data/e13m4p.cnf
#   b7343130b0577f810fcc32de15f952c96dd70338a2b0a55f75f5d50ca4d6651d  data/e13m4p.lrat  (11 MB; 61221 additions, 1305930 hints)
#   57adae5a317be75dbf5f37b205aab5266467164035493fe134a6715570101bac  data/e13m4n.cnf
#   5571336d9b9de232f87ae6fe9a552eb6f993b4646b3be2bf380fe3abc1fce379  data/e13m4n.lrat  (38 MB; 200702 additions, 4423243 hints)
python3 gen.py 2 A
./build.sh Cnf Store2 F2
./build.sh A00 A01 A02 A03 A04 A05 ; ./build.sh A06 A07 A08 A09 A10 A11    # two shells
./build.sh Steps2
python3 gen.py 4p P ; python3 gen.py 4n N
./build.sh Store4n F4n N00 N01 N02 N03 N04 N05 N06 N07                  # two shells
./build.sh Store4p F4p P00 P01 P02 P03 N08 N09 N10 N11
./build.sh Steps4p Steps4n
cd ../../.. && tools/leancheck-mathlib.sh NT/E13.1/E13_1_lrat.lean
```

`trim.py` keeps only the additions reachable from the empty clause through hints and renumbers
them consecutively after the input clauses. CaDiCaL is deterministic: the same CNF gives the
same LRAT file (rerun on `data/e13m2.cnf` checked 2026-11-07: same sha256 after trimming). The data only feed the stores; any LRAT proof of the same CNF works.

## Unsplit m = 4 (demonstration of the store without an id limit)

`E13Lrat/Unsplit4.lean` proves `cnf4_unsat_unsplit : Unsat (cnf 4 164)` from one store `S4` of
298 598 entries (ids beyond 2^18), the same statement as `cnf4_unsat` in `../E13_1_lrat.lean`.
The recorded proof stays the split one (it needs 7048 s of chunk-module kernel time against 7569 s).

```bash
cadical --lrat --binary=false data/e13m4.cnf data/e13m4.raw.lrat         # ~9 s
python3 trim.py 25287 data/e13m4.raw.lrat data/e13m4.lrat                # kept 273311, 6 132 487 hints
sha256sum data/e13m4.lrat
#   275af6ffc52171db45d68b774eb4a116b82c4789587f795895f4ff795d409555  data/e13m4.lrat  (53 MB)
python3 gen.py 4 U
./build.sh Store4 F4 U00 U01 U02 U03 U04 U05 U06 U07 ; ./build.sh U08 U09 U10 U11 U12 U13 U14 U15   # two shells, after Store4
./build.sh Steps4 Unsplit4
```

Checked 2026-11-08: `Store4` 60 s, 1.6 GB; `F4` 39 s, 5.4 GB; `U00..U15` 7569 s in total (182 to 514 s
each, peak 2.7 GB); `cnf4_unsat_unsplit` axioms propext, Classical.choice, Quot.sound.

The `.olean` files depend on `lib/build/OpenProblemsLib/LRAT.olean`: after `tools/buildlib.sh`
rebuilds `LRAT`, rebuild these modules too (all of them, in the order above).

Re-checked 2026-11-07 from scratch after the store packing change of `OpenProblemsLib.LRAT`: chunk modules
5906 s (m = 2) and 7048 s (m = 4 split), `E13_1_lrat.lean` OK. Checked 2026-11-07: all modules built with no warnings; `E13_1_lrat.lean` OK, `s_2_4` and `s_4_4`
axioms propext, Classical.choice, Quot.sound. Kernel time of the chunk modules: 5905 s (m = 2),
7361 s (m = 4, both halves of the split).
