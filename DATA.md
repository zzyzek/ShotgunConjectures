# External data

Some certificates scan published tables. The tables are not in this repository;
scripts look for them under `data/` at the repository root (or the path in the
environment variable each script names, e.g. `PSP_DATA`).

| file | contents | source |
|---|---|---|
| `data/psp2-annot-below-1e13.txt` | base-2 Fermat pseudoprimes below 10^13 with factorizations; `C` marks Carmichael numbers, `S` strong pseudoprimes | Feitsma–Galway list of base-2 pseudoprimes below 2^64, annotated version, <https://www.cecm.sfu.ca/Pseudoprimes/index-2-to-64.html> (`annotated-psps-below-2-to-64.txt.bz2`), lines with n < 10^13 |
| `data/pinch/c21.gz` | Carmichael numbers below 10^21 with factorizations | R. G. E. Pinch, Carmichael number tables, Zenodo record 13755236 (`c21.gz`) |

Each certificate README says which table it reads and how long the scan took.
