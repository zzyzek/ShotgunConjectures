# Sumner's universal tournament conjecture for n ≤ 5 (FAM-sumner-tournament)

Famous-problem pilot, problem 5 of 6. Date 2026-11-05. The conjecture is not settled.

## Statement

Sumner (1971): every tournament on 2n − 2 vertices contains every oriented tree on n vertices
(n ≥ 2). Known for all sufficiently large n (Kühn–Mycroft–Osthus 2011, threshold not explicit);
open for small n in general. Tight: the out-star on n vertices does not embed in a regular
tournament on 2n − 3 vertices.

## Result (Lean, `sumner_tournament_mathlib.lean`)

`SumnerSmall.sumner_le_five`: for 2 ≤ n ≤ 5, every tournament on 2n − 2 vertices contains every
oriented tree on n vertices. The statement has the same shape as formal-conjectures
`sumner_conjecture` with the bound n ≤ 5 added; the definitions `IsTournament`, `IsOrientation`,
`IsOrientedTree`, `Hom`, `Embeds` are copied verbatim from formal-conjectures (Mathlib has none of
them), with types `W V : Type` arbitrary finite types.

`Sumner4_mathlib.lean` is the same proof for n ≤ 4 (`SumnerSmall.sumner_le_four`); it checks in
about 7 s and is the quick regression file. `sumner_tournament_mathlib.lean` (1.4 MB, mostly data) checks in
in 560 s wall time (including queue wait) in one 6 GB slot.

Axioms (from `tools/leancheck-mathlib.sh`): propext, Classical.choice, Quot.sound for every
theorem (some use fewer). No sorry, no native_decide, zero warnings. The finite checks use
`decide +kernel` (the kernel evaluates the checker functions; no compiler, no `Lean.ofReduceBool`).

### Lean pieces

| Lean name | Statement in words | Kind |
|---|---|---|
| `tree_parent_code` | a finite tree on n vertices can be listed v_0, …, v_{n−1} (by distance from v_0) with a parent function par(i) < i for i > 0, such that every edge joins some v_i to v_{par(i)} | general |
| `classified_succ`, `classified_one` | if every tournament on Fin k is isomorphic to a listed representative and the extension table for k passes, the same holds for k + 1 | general |
| `codesOK_sound` | if `codesOK n` passes, every parent code (parent list plus direction bits) maps injectively, arc to arc, into a listed tree representative | general |
| `embBody_sound` | if `embBody n m i` passes, every tree representative embeds into tournament representative i | general |
| `sumner_of_checks` | the three checks for (n, m = 2n − 2) imply the conjecture for n | general |
| `step_k`, `emb_n`, `codes_n` | the finite checks, by `decide +kernel` | certificate |
| `classified_k` (k ≤ 8) | every tournament on k ≤ 8 vertices is isomorphic to one of 1, 1, 2, 4, 12, 56, 456, 6880 representatives | certificate |

## Argument

1. **Tree to code.** Root the tree at r; give every other vertex v a neighbour par(v) closer to r
   (from a shortest walk). The n − 1 edges {v, par(v)} are distinct (the parent is strictly
   closer) and the tree has n − 1 edges (Mathlib `IsTree.card_edgeFinset`), so these are all the
   edges. Sorting vertices by distance (Mathlib `Tuple.sort`) gives par(i) < i. An orientation is
   then a parent code: parent list p_i < i and one direction bit per non-root vertex
   ((n − 1)!·2^(n−1) codes: 1, 2, 8, 48, 384 for n = 1..5).
2. **Code to tree representative.** For every code, a certificate (representative index and an
   injective relabelling) maps code arcs to arcs of one of 1, 3, 8, 27 oriented-tree
   representatives (n = 2..5).
3. **Tournament classification.** A tournament on Fin (k+1) restricted to Fin k is, by induction,
   isomorphic to representative i; the last vertex adds an in-set S ⊆ {0..k−1}, encoded as a
   number S < 2^k. For every (i, S) the table gives a representative j on k + 1 vertices and a
   permutation; the kernel checks that it is an isomorphism (pairs a < b only; the other pairs
   follow by antisymmetry, proved). Tables: 2^k × (number of representatives on k) entries,
   58 368 entries for k = 7.
4. **Embeddings.** For every tournament representative on 2n − 2 vertices and every tree
   representative, an explicit injective map is checked arc by arc (6880 × 27 = 185 760 maps for
   n = 5).

The representative lists need not be repeat-free, and nothing about the generator is trusted:
only its output is checked.

## Outside Lean

* certificate/gen.py N`: builds the representatives (canonical form by degree refinement and
  permutations within cells), checks Sumner for n ≤ N by backtracking (n = 5: 0 failures over
  6880 × 27 pairs, 9 s). Counts match OEIS A000568 (tournaments 1, 1, 2, 4, 12, 56, 456, 6880) and
  A000238 (oriented trees 1, 1, 3, 8, 27).
* certificate/gen_lean.py N`: emits the data section; certificate/build_lean.py N DATA` assembles
  the Lean file from certificate/parts/` (header, checkers `comp.lean`, soundness `glue.lean`).
  Rebuild: `python3 gen_lean.py 5 > /tmp/d.lean; python3 build_lean.py 5 /tmp/d.lean > ../sumner_tournament_mathlib.lean`.

## Obstacles

* **n = 6 by the same certificate.** Needs tournaments on 10 vertices: 9 733 056 classes, an
  extension table 9 → 10 of 191 536 × 512 ≈ 9.8 × 10^7 entries, and 9.7 × 10^6 × 91 embeddings.
  Measured kernel throughput: about 5 × 10^4 trivial `Nat.rec` loop steps per second; the n = 5
  file (5.8 × 10^4 table entries + 1.9 × 10^5 embeddings) took under 10 minutes and needed the
  checks split into 19 + 20 theorems to stay under 6 GB (kernel caches are per declaration).
  n = 6 is about 1000 times larger: out of reach for a kernel certificate. Even n = 5 required
  recursor-based loops and `Nat.blt`/`Nat.beq`/`cond` instead of `Decidable` instances.
* **Smarter route not attempted.** The known small-case proofs are structural: Havet–Thomassé
  median orders (arborescences, 2000), Céroi–Havet (trees with at most 4 leaves, which covers all
  n ≤ 5 and all n = 6 trees except stars), Reid–Wormald (caterpillars of diameter ≤ 4, which
  include stars). Formalising median orders (an order maximising forward arcs and its "feedback
  property") is the natural next tool; it would also give the FC `el_sahili` (3n − 3) and
  arborescence variants, which FC states with sorry.

## Literature and formalisation checked (2026-11-05)

* formal-conjectures `FormalConjectures/Wikipedia/SumnerUniversalTournamentConjecture.lean`
  (main, fetched 2026-11-05): conjecture (open), KMO large n, El Sahili 3n − 3, sharpness, all
  with sorry. No small-n statement. `FormalConjecturesForMathlib/Combinatorics/Digraph/Tournament.lean`
  defines `IsTournament`, `IsOrientation`, `Hom`.
* OpenAI math repository (`~/claude/openai-math/repo`, CONTENTS.md and `lean/`): no tournament or
  Sumner item.
* Mathlib: `Digraph` basics only; no tournaments or orientations.
* Web search (Wikipedia "Sumner's conjecture", KMO arXiv:1010.4430, Mycroft–Naia
  arXiv:1609.03393): no published exhaustive computer check for specific n was found, and no
  Lean formalisation. Small n follows from Céroi–Havet (≤ 4 leaves) for n ≤ 5.

## New or known

Known: n ≤ 5 follows from Céroi–Havet (trees with at most 4 leaves) and from simple computer
search (done here in 9 s). New as far as the checks go: a machine-checked proof, in the FC
statement shape, for n ≤ 5; and the general Lean lemmas (tree parent codes, tournament
classification by one-vertex extension) that any later certificate can reuse.

`sumner_tournament4_mathlib.lean` is the same proof for n <= 4 (`sumner_le_four`), which checks in seconds.
