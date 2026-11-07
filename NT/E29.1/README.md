# Guy E29: Graham's {x, y, x+y, xy} colouring threshold starting at 3 is 3150

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section E29.
Graham showed that every 2-colouring of [1, 252] contains x, y, x + y, xy of one colour (and 252 is
least), and asked about the analogous thresholds when the interval starts later.

**Reading.** x < y, both in the interval, and x, y, x + y, xy all in the interval and of one colour.
This convention reproduces Graham's 252 for the interval starting at 1 (x = 1 gives the triple
{1, y, y + 1}) and gives 990 starting at 2. Allowing x = y instead gives 39 and 450. From 3 on the
four numbers are automatically distinct, so the two readings that require distinctness agree.

**Result.** The least N such that every 2-colouring of [3, N] has x < y with x, y, x + y, xy
monochromatic is N = 3150.

**Argument.** Lower bound: an explicit colouring of [3, 3149] with no monochromatic quadruple.
Upper bound: the CNF with one variable per n in [3, 3150] and, for every x < y with xy ≤ 3150, the
two clauses "not all false" and "not all true" on {x, y, x + y, xy} is unsatisfiable.

**Evidence.**
- Lean, whole result: [`E29_1_lrat.lean`](E29_1_lrat.lean), theorem `forces_iff : Forces N ↔ 3150 ≤ N`
  for every N, where `Forces N` says every 2-colouring has x < y with x ≥ 3, xy ≤ N and x, y, x + y, xy of
  one colour. Axioms propext, Classical.choice, Quot.sound; no native_decide.
  - Upper bound `forces_3150`: the CNF `cnf 3150` is defined from the problem by a Lean function
    ([`lrat/E29Lrat/Cnf.lean`](lrat/E29Lrat/Cnf.lean), encoding lemma `forces_of_unsat`), and is proved
    unsatisfiable with the library checker `OpenProblemsLib.LRAT` (guide `lib/docs/lrat.md`): the kernel
    checks that the clause store begins with `cnf 3150` and that all 126 702 additions of a CaDiCaL 2.1.3
    LRAT proof (2.99 million hints) are RUP, in 375 chunk theorems over 8 modules
    ([`lrat/README.md`](lrat/README.md)): about 62 min of checking in total (8 chunk modules of
    245 to 494 s, peak memory 3.1 GB each; store build and `store_cnf` 23 s each).
    The LRAT file (24 MB) is not in git; `lrat/README.md` regenerates it (CaDiCaL is deterministic).
  - Lower bound `not_forces_3149`: the explicit colouring of [3, 3149] from
    [`E29_1.lean`](E29_1.lean) (core Lean, theorem `no_mono`).
  Outside Lean: the reading of Guy's question as `Forces` (x < y, interval starting at 3; see Reading).
- Earlier, independent checks of the upper bound:
  [`certificate/unsat_3_3150.cnf.gz`](certificate/unsat_3_3150.cnf.gz) (3150 variables,
  16378 clauses) and the DRAT proof [`certificate/unsat_3_3150.drat.gz`](certificate/unsat_3_3150.drat.gz)
  written by CaDiCaL 1.5.3, checked by [`certificate/rupcheck.c`](certificate/rupcheck.c), a forward DRAT
  checker written independently of the solver: all 111 246 lemmas are RUP and the empty clause is derived
  ([`certificate/rupcheck.log`](certificate/rupcheck.log), 3.8 s). The checker rejects an empty proof, the
  proof with its first 20 000 lemmas removed, and the formula with 10% of its clauses removed.
- [`certificate/recheck.py`](certificate/recheck.py) regenerates the clause set from the definition
  and confirms it equals the CNF, re-checks the colouring by brute force, and gets UNSAT from
  Lingeling, MiniSat 2.2 and MapleChrono; CaDiCaL and Glucose agree.
  [`certificate/sat.py`](certificate/sat.py) is the incremental threshold search,
  [`certificate/certify.py`](certificate/certify.py) wrote the CNF, model and proof.

To re-run the DRAT check:

```bash
gcc -O2 -o rupcheck certificate/rupcheck.c && zcat certificate/unsat_3_3150.cnf.gz > f.cnf && zcat certificate/unsat_3_3150.drat.gz > p.drat && ./rupcheck f.cnf p.drat
```

**Review level.** `lean-proof` (both bounds proved in Lean; the upper bound by a kernel-checked LRAT certificate, 2026-11-07).
**Prior art.** No value for the interval starting at 3 found: [Bowen, arXiv 2205.12921](https://arxiv.org/abs/2205.12921) and later papers cite only Graham's 252 and Hindman's 990; [Green–Sawhney, arXiv 2511.09365](https://arxiv.org/abs/2511.09365) treat {x+y, xy} only. Searched: web for the thresholds and 3150. Verdict: new. 2026-11-04.
