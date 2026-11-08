# Guide for agents filling this repo

Goal: one directory per resolved problem with a self-contained README, the
evidence, and a Lean check where core Lean can do it. You are also the
**second reader** of each result: re-derive it before writing it up. If it
does not hold up, say so (`"disputed": true` plus a note); do not paper over it.

Worked examples (copy their shape):
- `OEIS/A100682/` with `OEIS/A100682/A100682.lean` (witness facts)
- `COM/C125/` with `COM/C125/C125.lean` (a "for all n" proof:
  finitely many `decide` facts + one periodicity lemma). For any covering
  argument use the generator: `oplib.lean.covering_file(...)` in
  `methods/oplib/lean.py` (F(n) = A*b^n + C with A, C ≥ 1; adapt by
  hand for other shapes, e.g. |2^m − p|).

## Inputs

- `problems.jsonl`: your records (id, title, result, summary from the scan).
- The scan repo `../open-problems`: `triage/*.jsonl` (full record), `notes/<id>.md`
  (deep notes), `scratch/`, `work/<id>/`, `audit/scripts/` (scripts that produced
  the result), `text/` (source texts; book text is copyrighted, paraphrase it),
  `docs/METHODS.md`. The methods library is in this repo: `methods/` (one README per
  method) and `methods/oplib/`.

## Per problem

1. `<SRC>/<REST>/README.md` (`REST` = id without the `SRC-` prefix) with sections: title line, **Source** (citation;
   OEIS text may be quoted with the A-number, book text paraphrased with
   section), **Reading** (only if a convention or interpretation choice
   matters), **Result**, **Argument** (short, complete), **Evidence** (Lean file,
   scripts, what is outside Lean), **Review level**, **Prior art** (what was
   checked, with date). The prior-art search always includes
   google-deepmind/formal-conjectures (a `research solved` tag with a
   `formal_proof` link means someone has a Lean proof) and, for Erdős problems,
   the teorth/erdosproblems wiki "AI contributions to Erdős problems".
2. Copy the scripts that produced or check the result into `certificate/`
   (small files only; no data files over 1 MB; published tables are read from `data/`, see DATA.md).
3. Lean, core only (no `import Mathlib`), in `<SRC>/<REST>/<M>.lean`
   (M = REST with `.` and `-` replaced by `_`). Good fits: explicit counterexamples,
   factorizations, finite enumerations bounded by a constant, covering
   arguments, identities checked by `decide`, small `omega`/`simp` proofs.
   Do not use `native_decide`. Every file has a header comment stating what is
   and is not checked. Keep `decide` searches bounded by explicit small
   constants (the kernel recursion limit bites on `List.range (n+1)` for n in
   the hundreds).
4. Check with `tools/leancheck.sh <file>` only. It serialises all Lean runs on
   the machine (another job has priority); never call `lean` or `lake` directly.
5. Use Mathlib and the shared library (`lib/OpenProblemsLib`, `lib/PNTPlus`,
   guides in `lib/docs`) freely; check with `tools/leancheck-mathlib.sh`.
   If a definition or an elementary lemma is missing (a sequence, a number
   family, a finite-sum identity, a determinant or rank argument), build it:
   that is part of the proof, not a blocker. Set
   `"lean_status": "needs-mathlib"` only when a named, substantial theorem is
   missing from Mathlib and the library (for example Kepler, Dusart's explicit
   bounds, Deligne, Mazur, the class number formula, transfer theorems), and
   say in the notes which theorem and why building it is out of scope; list it
   in `depends_on`. The deepest results of a round get the Lean pass first.
6. Trivial or misstated items: README explaining the triviality or the
   misstatement; Lean if a one-line `decide` captures it.

## Recording status

Append one JSON object per problem to `updates/<your-group>.jsonl` (never edit
`problems.jsonl`; `tools/manifest.py` merges; then run `tools/build_readmes.py` to regenerate the group READMEs):

```json
{"id": "COM-C004", "lean": "COM/C004/C004.lean", "lean_status": "checked",
 "review": "lean-witness", "certificate": "COM/C004/certificate",
 "depends_on": [], "disputed": false, "notes": "outside Lean: none"}
```

`lean_status`: `checked` | `needs-mathlib` | `none` (no Lean meaningful) | `failed`.
`review`: `agent` (you could not re-derive it), `rechecked` (you re-derived it
by other means), `lean-witness`, `lean-proof` (see README.md).

## Resource limits

The user has a higher-priority job. Python checks: single process,
`nice -n 19`, `ulimit -v 2000000`, `timeout 300`. Lean only via
`tools/leancheck.sh`. No web fetches unless needed to confirm a citation.

## Methods

Tag each problem with up to four method slugs from `methods/methods.json`
(primary first) in the `"methods"` field of its update line. A new method
gets a directory `methods/<slug>/README.md` with the same front matter as
the others and an entry in `methods/methods.json`.

## Mathlib proofs

A problem whose argument needs Mathlib gets `<SRC>/<REST>/<M>_mathlib.lean`
beside any core file (keep the core file). Build the shared library first
(`tools/buildlib.sh`), then check only with `tools/leancheck-mathlib.sh`
(3 concurrent runs machine-wide, 6 GB each). Use `lib/OpenProblemsLib`:
`powMod`, Pratt certificates (`tools/pratt_cert.py` emits them;
`prime_of_prattCertifies`), `pspCheck`, Korselt (`isCarmichael_of_factors`,
`korselt_necessary`), Cipolla. Repetitive files come from templates
`certificate/<M>_mathlib.lean.in` expanded by `tools/lean_expand.py`.
A header comment line must not start with `theorem` in column 0 (the check
script greps declarations). Record the result in `updates/z-*.jsonl` (the
`z-` prefix makes it sort after the older update files).

## Core questions

When an attempt fails, check `methods/cores.jsonl` and `methods/attempts.jsonl` for the same obstacle. If two
or more attempts share it, draft a core question: a smaller, sharper question (not a broader framework) whose
answer settles or reduces all of them. It must pass three tests: leverage (at least two problems), strictly
easier (a bounded or finite version, or a known method reaches it), checkable (a numerical test, run and
recorded in `check`). Record it with status `proposed`; list it in your report. A core that is only a
generalisation of the problems fails the "easier" test.
