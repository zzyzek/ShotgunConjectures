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
- Lean: [`E29_1.lean`](E29_1.lean), theorem `no_mono`: under the colouring `colour` (bits of one
  natural number), no x ≥ 3, x < y, xy ≤ 3149 has x, y, x + y, xy of one colour. Core Lean;
  `allOk_53` uses no axioms, the others propext and Quot.sound.
  Outside Lean: the upper bound.
- Upper bound: [`certificate/unsat_3_3150.cnf.gz`](certificate/unsat_3_3150.cnf.gz) (3150 variables,
  16378 clauses) and the DRAT proof [`certificate/unsat_3_3150.drat.gz`](certificate/unsat_3_3150.drat.gz)
  written by CaDiCaL 1.5.3. [`certificate/rupcheck.c`](certificate/rupcheck.c) is a forward DRAT
  checker (every lemma checked, RUP and RAT) written independently of the solver: all 111 246 lemmas
  are RUP and the empty clause is derived ([`certificate/rupcheck.log`](certificate/rupcheck.log),
  3.8 s). The checker rejects an empty proof, the proof with its first 20 000 lemmas removed, and the
  formula with 10% of its clauses removed. Not checked by a formally verified checker
  (drat-trim / cake_lpr).
- [`certificate/recheck.py`](certificate/recheck.py) regenerates the clause set from the definition
  and confirms it equals the CNF, re-checks the colouring by brute force, and gets UNSAT from
  Lingeling, MiniSat 2.2 and MapleChrono; CaDiCaL and Glucose agree.
  [`certificate/sat.py`](certificate/sat.py) is the incremental threshold search,
  [`certificate/certify.py`](certificate/certify.py) wrote the CNF, model and proof.

To re-run the DRAT check:

```bash
gcc -O2 -o rupcheck certificate/rupcheck.c && zcat certificate/unsat_3_3150.cnf.gz > f.cnf && zcat certificate/unsat_3_3150.drat.gz > p.drat && ./rupcheck f.cnf p.drat
```

**Review level.** `lean-witness` (lower bound proved in Lean; upper bound DRAT-checked by our own checker).
**Prior art.** No value for the interval starting at 3 found: [Bowen, arXiv 2205.12921](https://arxiv.org/abs/2205.12921) and later papers cite only Graham's 252 and Hindman's 990; [Green–Sawhney, arXiv 2511.09365](https://arxiv.org/abs/2511.09365) treat {x+y, xy} only. Searched: web for the thresholds and 3150. Verdict: new. 2026-11-04.
