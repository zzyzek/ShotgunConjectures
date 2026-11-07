# External data

Some certificates scan published tables. The tables are not in this repository;
scripts look for them under `data/` at the repository root (or the path in the
environment variable each script names, e.g. `PSP_DATA`).

| file | contents | source |
|---|---|---|
| `data/psp2-annot-below-1e13.txt` | base-2 Fermat pseudoprimes below 10^13 with factorizations; `C` marks Carmichael numbers, `S` strong pseudoprimes | Feitsma–Galway list of base-2 pseudoprimes below 2^64, annotated version, <https://www.cecm.sfu.ca/Pseudoprimes/index-2-to-64.html> (`annotated-psps-below-2-to-64.txt.bz2`), lines with n < 10^13 |
| `data/pinch/c21.gz` | Carmichael numbers below 10^21 with factorizations | R. G. E. Pinch, Carmichael number tables, Zenodo record 13755236 (`c21.gz`) |
| `data/amicable/c2_filtered.7z` | all known amicable pairs up to 30 digits and the known longer ones except types (3,2) to (10,2); complete for smaller member below 10^20, with factorizations, 10 221 707 pairs, as of 2023-01-01 (md5 c20d76d6d851a9afba8bd671b1985e59) | S. Chernykh, Amicable pairs list, <https://sech.me/ap/> (`compressed/c2_filtered.7z`, "non-trivial pairs") |

Each certificate README says which table it reads and how long the scan took.
