# LRAT: kernel-checked unsatisfiability certificates

Module: `LRAT.lean` (core Lean only; no Mathlib).

## 1. The method

A SAT solver that reports UNSAT can also write a proof: a list of derived clauses, each with the ids
of the earlier clauses that make it follow by unit propagation (LRAT format, RUP steps). The
module checks such a proof in the Lean kernel by `decide +kernel` and turns a successful check into
the theorem `Unsat F` for the CNF `F` named in the statement. The proof data are untrusted input:
a wrong proof makes the check return `false`, it cannot prove a false statement.

**Notation.** A CNF is `F : List (List Nat)`. Literal code `k` is variable `k / 2`, positive iff `k`
is even (DIMACS `d` becomes `2d`, `-d` becomes `2d + 1`). A valuation is `v : Nat → Bool`;
`litT v k`, `csat v c` (some literal of `c` true), `Satisfies v F` (every clause), and
`Unsat F` (no `v` satisfies `F`).

**The clause store** `S : T` is a binary trie keyed by clause id. Entries `1..m` should be the
clauses of `F`, entries `m+1..last` the derived clauses, each with its hint list. The reader
`lratStore% "f.cnf" "f.lrat"` builds it from a DIMACS file and a text LRAT file; each entry is
two `Nat`s packing the clause and the hints, so the data stay small terms.

**Packing** (`unpack`). A packed list `w` has a width `b = w % 64` in its low 6 bits; the rest,
`w / 64`, holds the length and then the entries as base-`2^b` digits, lowest first. The reader
picks for each list the bit length of its largest number (length included), so literal codes,
clause ids and lengths may be anything below `2^63`, and each list is no larger than its widest
number needs. Until 2026-11-07 the base was a fixed `2^18`, which limited stores to 262 143
entries (NT-E13.1 split its m = 4 proof and NT-E11.2 reran the proof on an unsat core because of
it). A fixed base `2^32` was tried first and rejected: it made the E29.1 benchmark module 38%
slower and the store elaboration 6 times slower, because every packed number grows by 32/18.

Measured 2026-11-07, base `2^18` against per-entry width (same machine, quiet): GEO-E4.4 whole
file 20.8 s against 19.9 s; E29.1 module `C07` 239 s against 241 s, peak 3.0 GB both; E29.1 store
elaboration 23 s against 26 s. The reader does slightly more work per entry, so a store module of
more than about 200 000 entries (NT-E11.2, NT-E13.1 m = 2) needs `set_option maxHeartbeats 1000000 in` before its
`lratStore%` definition (elaboration heartbeats; the kernel check is not affected). Re-check of all
users from scratch with the new packing (2026-11-07, two modules at a time): NT-E29.1 chunk modules
3681 s, NT-E13.1 12 954 s (m = 2: 5906 s; m = 4 split: 7048 s), NT-E11.2 5142 s; all final files
OK with axioms propext, Classical.choice, Quot.sound. Demonstration of the removed limit: the
unsplit NT-E13.1 m = 4 proof, one store of 298 598 entries (25 287 clauses, 273 311 additions,
6 132 487 hints), checks in 16 chunk modules (7569 s, peak 2.7 GB) plus the CNF check `F4`
(39 s, 5.4 GB); `NT/E13.1/lrat/E13Lrat/Unsplit4.lean`.

**Theorem** (`LRAT.lean`).

1. `unsat_of_parts`: if `F.length = m`, `chkF S F 1 = true` (entries `1..m` are `F`, in order),
   `steps S (m + 1) k = true` with `k > 0` (entries `m+1..m+k` are each RUP from the entries
   before them), and `lastEmpty S (m + k) = true` (entry `m + k` is the empty clause), then
   `Unsat F`.
2. `check_sound`: the same with one Boolean `check F S last`.
3. `steps_add`, `steps_join`: `steps S n a` and `steps S (n + a) b` give `steps S n (a + b)`. So a long
   proof is checked as many theorems `steps S n k = true`, each its own kernel declaration (kernel
   memory is released between declarations), in as many files as needed, and joined at the end.

**Trusted surface.** The definitions `litT`, `csat`, `Satisfies`, `Unsat`, the statements of
`unsat_of_parts` and `check_sound`, and the CNF `F` in the final statement (best defined by a
Lean function from the problem, with an encoding lemma). Not trusted: the store, the readers,
the solver, the LRAT file, the chunking.

## 2. When to reach for it

- A finite combinatorial statement reduced to UNSAT of a CNF: Ramsey-type and van der Waerden-type
  thresholds, colouring problems, Schur-type numbers, finite geometry via order types. The
  threshold's lower bound is usually an explicit witness (a `decide` check); the upper bound is UNSAT.
- Proof sizes: about 1.1 ms of kernel time per hint and about 0.3 GB of kernel memory per 1000
  hints inside one declaration (measured on NT-E29.1). Chunks of 8000 hints stay near 2 GB, so
  the 6 GB cap of `tools/leancheck-mathlib.sh` is never the limit; time is. A proof with 3 million
  hints is about an hour of kernel time, spread over files of at most 400 000 hints (about 8 min each).
- Not for RAT steps (negative hints): use a solver mode without RAT (CaDiCaL's LRAT output is RUP
  only) or convert the proof with an external tool first. Not for DRAT without hints: convert to
  LRAT (`drat-trim -L`, or rerun CaDiCaL with `--lrat`).
- For small proofs (under 0.1 MB of LRAT) Mathlib's `lrat_proof` also works and needs no data files;
  it builds one term and runs out of memory at a few MB.

**Producing LRAT.** `cadical --lrat --binary=false f.cnf f.lrat` (CaDiCaL 2.1.3, deterministic:
the same input gives the same file). Ids are consecutive after the `m` input clauses, deletions are
written as `id d ...` lines and are ignored by the reader (they only matter for speed of other
checkers, never for soundness).

## 3. Paper proof

Fix a valuation `v` satisfying `F`. Call an assignment `A` (a set of literal codes, as a bitmask)
*good* if every literal in `A` is true under `v`.

**Unit propagation (`unit`, `prop`).** For a clause `c` and good `A`, `unit A c` scans `c`: a literal
whose negation is in `A` is false under `v`. If all literals are false (`some none`), `c` is false
under `v` (`unit_conf`). If exactly one literal `k` is not known false (`some (some k)`) and `c` is
true under `v`, then `k` is true under `v` (`unit_unit`), so `A ∪ {k}` is good. `prop` follows the
hint list: each hinted clause must be unit (add its literal) or, for the last hint, conflicting.
If every hinted clause is true under `v`, a good `A` can never reach a conflict, so
`prop = true` is impossible from a good start (`prop_sound`).

**RUP (`rup_sound`).** To show `C` true under `v`: if it were false, the assignment of all negated
literals of `C` (`negAll`) is good, the hinted clauses are true under `v`, and `prop` reaches a
conflict, contradicting the previous paragraph.

**Induction over the store (`steps_sound`).** `Ent v S n`: every stored clause with id in
`[1, n)` is true under `v`. `chkF S F 1` makes entries `1..m` equal to the clauses of `F`, so
`Ent v S (m + 1)` (`chkF_sound`). If `Ent v S n` and entry `n` is RUP from the entries with ids in
`[1, n)` (`below`), then entry `n` is true under `v`, so `Ent v S (n + 1)`. After `k` steps
`Ent v S (m + k + 1)`, so entry `m + k`, the empty clause, is true under `v`: impossible. Hence no
`v` satisfies `F`.

**Chunking (`steps_add`).** `steps S n (a + b)` is by definition the conjunction of the `a + b`
single steps, which is `steps S n a && steps S (n + a) b`; induction on `a`.

**Kernel efficiency.** The checked functions use recursors (`List.rec`, `Nat.rec`, `T.rec`) and
`Nat.beq`/`Nat.ble` instead of structural recursion and decidable `if`: the kernel reduces them by
plain iota steps, without `brecOn` tuples, about twice as fast. The assignment is one `Nat`
(GMP-accelerated `|||`, `<<<`, `testBit` in the kernel). None of this affects the statements.

## 4. Worked example: GEO-E4.4 (Birch's 8-point question, SAT part)

**Claim.** The CNF of `GEO/E4.4/certificate/e44_sat.py` (616 variables, 9800 clauses: signotope
axioms on the orientations of 8 x-sorted points, Tseitin variables for "segment meets open
triangle", one clause per partition into a segment and two triangles) is unsatisfiable.

**Data.** `cadical --lrat --binary=false e44.cnf e44.lrat`: 0.03 s, 62 KB, 625 additions, 7890 hints.
Check: 20 s, 2.0 GB for the whole file. A CNF read by `dimacs%` must be a `noncomputable def`
(the compiler hits its recursion limit on a 9800-clause literal).

**Lean.** `GEO/E4.4/E4_4_lrat.lean`:

```lean
noncomputable def birchCnf : List (List Nat) := dimacs% "GEO/E4.4/certificate/e44.cnf"
noncomputable def store : T :=
  lratStore% "GEO/E4.4/certificate/e44.cnf" "GEO/E4.4/certificate/e44.lrat"
theorem birch_len : birchCnf.length = 9800 := by decide +kernel
theorem birch_store : chkF store birchCnf 1 = true := by decide +kernel
theorem birch_last : lastEmpty store 10425 = true := by decide +kernel
theorem s9801 : steps store 9801 225 = true := by decide +kernel
-- ... three more chunks, joined by `steps_join` into `birch_steps`
theorem birch_cnf_unsat : Unsat birchCnf :=
  unsat_of_parts birchCnf store 9800 625 birch_len birch_store (by decide) birch_steps birch_last
```

Here the CNF is read from the file (`dimacs%`), so the statement is about that file; the geometry
(that every 8-point set in general position satisfies the CNF) is outside Lean.

**Larger example: NT-E29.1** (`NT/E29.1/E29_1_lrat.lean`, `NT/E29.1/lrat/`). The CNF is
`E29Lrat.cnf 3150`, a Lean function of the problem with the encoding lemma `forces_of_unsat`;
the store's first 16 378 entries are checked equal to it (`store_cnf`, 23 s). The 126 702 additions
(2.99 million hints) are 375 chunk theorems in 8 modules compiled by `NT/E29.1/lrat/build.sh`,
joined in `E29Lrat.Steps`; the final file proves `forces_iff : Forces N ↔ 3150 ≤ N`.
Kernel time 3681 s for the steps (8 modules of 247 to 503 s), peak 3.1 GB per module (re-check
2026-11-07 with the per-entry packing; 3647 s with the old fixed base).

## 5. Lean names

| name | statement or role |
|---|---|
| `litT`, `csat`, `Satisfies`, `Unsat` | semantics (trusted) |
| `T`, `get`, `unpack` | the clause store and its packed entries (per-entry digit width) |
| `unit`, `prop`, `negAll`, `rup` | unit propagation along the hints |
| `rup_sound` | RUP from true clauses gives a true clause |
| `chkF`, `chkF_sound` | entries `j..j+|F|-1` of the store are `F` |
| `steps`, `steps_sound` | consecutive entries are RUP in turn |
| `steps_add`, `steps_join` | chunks compose (the second with literal arithmetic by `rfl`) |
| `lastEmpty` | the last entry is the empty clause |
| `unsat_of_parts` | the four pieces give `Unsat F` |
| `check`, `check_sound` | the whole check as one Boolean |
| `lratStore%`, `lratLast%`, `dimacs%` | readers (untrusted; build terms from files at elaboration time) |

All in namespace `OpenProblemsLib.LRAT`; axioms propext, Classical.choice, Quot.sound.
Used by NT-E29.1, NT-E13.1, NT-E11.2 and GEO-E4.4.
