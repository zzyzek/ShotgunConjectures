# Dean's conjecture, k = 5 status and longest-path lemmas in Lean (FAM-dean-cycles)

Famous-problem round 2, 2026-11-05. The conjecture is not settled here; the open case k = 5 was
not reached.

## Source

Dean (1988; Bondy's survey, Conjecture 7.4): for every k ≥ 3, every finite simple graph with
minimum degree at least k has a cycle whose length is divisible by k. MathWorld
`DeansConjecture.html`; formal-conjectures `FormalConjectures/Arxiv/2605.02731/DeanCycles.lean`
(fetched 2026-11-05): `dean_conjecture` and `dean_conjecture.variants.five` tagged
`research open`; `variants.three`, `variants.four`, `variants.six_le` tagged `research solved`;
all with `sorry`, no `formal_proof` link.

## Literature status (checked 2026-11-05)

| case | status | source |
|---|---|---|
| k = 3 | proved; even with δ ≥ 2 and at most one vertex of degree 2 | Chen–Saito, JCTB 60 (1994) 277–292 |
| k = 4 | proved; δ ≥ 2 and at most two vertices of degree 2 | Dean–Lesniak–Saito, Discrete Math. 121 (1993) 37–49 |
| k = 3, 4, sharper | full characterisation with at most three degree-2 vertices | Choi–Chu–Kim–Park, arXiv:2605.02731 (4 May 2026) |
| k ≥ 6 | proved | Luo–Ma–Zhao, arXiv:2601.13552 (20 Jan 2026); footnote: "The case k = 5 requires separate arguments ... forthcoming work" |
| k = 5 | open (published sources) | LMZ abstract and footnote; Choi et al. abstract ("known ... for all k ≠ 5") |
| k = 5, claimed | proof claimed, unverified | Botsford, Zenodo 10.5281/zenodo.22182448 (31 Aug 2026, AI-assisted) with a computational supplement; MathWorld (as of 7 Sep 2026) lists the reductions as independently unverified |

Weaker k = 5 statements that are already known:

* minimum degree ≥ 6: Gao–Huo–Liu–Ma (IMRN 2022, arXiv:1904.08126) prove that minimum degree
  ≥ k + 1 gives cycles of every even length mod k; for odd k = 5 the even residues 0, 2, 4, 6, 8
  cover all classes, so a cycle of length ≡ 0 (mod 5) exists.
* 5-connected graphs: Gao–Huo–Liu–Ma (Dean's weaker conjecture).
* 2-connected graphs with minimum degree ≥ 5: Bai–Grzesik–Li–Prorok, arXiv:2511.03085, JCTB 180
  (2026) 111–150: for 2-connected G with δ ≥ k ≥ 4, cycles of every even length mod k unless
  G = K_{k+1} or K_{k,n−k}; both exceptions have cycles of length divisible by 5 (K_6 has C_5,
  K_{5,m} has C_10).
* minimum degree ≥ 10: immediate from LMZ with k = 10.

## Result (Lean, `dean_cycles_mathlib.lean`)

All statements are known; they are infrastructure in the formal-conjectures shape (`cycleLengths`
copied from FC), not progress on k = 5.

| Lean name | Statement in words |
|---|---|
| `cycle_of_two_neighbours` | if `p` is a path starting at `u` and `u` is adjacent to the vertices at positions `1 ≤ i < j ≤ length p`, then `G` has a cycle of length `j − i + 2` |
| `exists_path_nbrs_mem` | a finite graph on a nonempty vertex type has a path from some `u` that contains every neighbour of `u` (a longest path) |
| `exists_cycle_mod_two` | for `k ≥ 1`, minimum degree `≥ k + 1` gives a cycle of length `≡ 2 (mod k)` |
| `exists_cycle_mod_two_five` | minimum degree `≥ 6` gives a cycle of length `≡ 2 (mod 5)` |
| `exists_cycle_length_ge` | for `k ≥ 2`, minimum degree `≥ k` gives a cycle of length `≥ k + 1` |

Axioms (from `tools/leancheck-mathlib.sh`, 2026-11-05): propext, Classical.choice, Quot.sound for
every theorem. No sorry, no native_decide, zero warnings. Check time about 10 s.

## Argument

Take a longest path P = v_0 v_1 … v_m. Every neighbour of v_0 lies on P (otherwise P extends). If
v_0 is adjacent to v_i and v_j with 1 ≤ i < j, then v_0 v_i v_{i+1} … v_j v_0 is a cycle of length
j − i + 2. With δ ≥ k + 1 there are k + 1 neighbour positions, two of them congruent mod k, giving a
cycle of length ≡ 2 (mod k). The neighbour v_1 and the farthest neighbour (position ≥ k when
δ ≥ k) give a cycle of length ≥ k + 1.

## Outside Lean

Nothing for the Lean statements. The literature table and the reduction below are on paper.

**Reduction (standard, on paper).** k = 5 holds iff every 2-connected graph B in which all
vertices except at most one (the root c) have degree ≥ 5 has a cycle of length ≡ 0 (mod 5).
(If G has δ ≥ 5, every cycle lies in a block; if G is 2-connected use B = G, otherwise an
end-block B has at most one cut vertex c and all other vertices keep their ≥ 5 neighbours inside
B. Conversely, gluing five copies of such a B at c gives a graph with δ ≥ 5 whose cycles are the
cycles of the copies.) Bai–Grzesik–Li–Prorok settle the case with no root; Chiba–Yamashita's
admissible-cycle theorem allows two exempt vertices but needs degree ≥ k + 1 = 6 elsewhere. The
rooted case with degree exactly 5 is what LMZ handle for k ≥ 6 with trigonal/tetragonal cores and
defer for k = 5.

## Obstacles

* **Longest-path chords cannot force 0 (mod k).** From a longest path the cycles visible without
  further structure have lengths p_j − p_i + 2 (chords from one end), q_j − q_i + 2 (other end),
  q + m − p + 2 (crossing chords q < p) and q − p_i + m − p_j + 3 (p_i ≤ q < p_j). If all chord positions from v_0 are ≡ 1 and all from
  v_m are ≡ m − 1 (mod 3) with m ≡ 1 (mod 3), every such length is ≡ 2 (mod 3), at any minimum
  degree. So the k = 3 case, and k = 5, need block/ear structure (Chen–Saito; admissible paths of
  Gao–Huo–Liu–Ma; LMZ cores), not path bookkeeping.
* **No new k = 5 weaker form within reach.** The natural weakenings (δ ≥ 6, 5-connected,
  2-connected, δ ≥ 10) are all known (table above). What remains is the rooted 2-connected case,
  which is exactly the part LMZ say needs separate arguments.
* **Chen–Saito in Lean not attempted beyond infrastructure.** The proof (14 pages, JCTB 1994; the
  2026 strengthening by Choi et al. is about 10 pages) is a minimal-counterexample analysis over
  blocks, ears and path lengths mod 3. Mathlib has walks, paths and cycles but no block/cut-vertex
  decomposition or ear decomposition. A formalisation is a multi-thousand-line project, outside
  the time box. The lemmas above are the first layer it would use.

## Prior art (2026-11-05)

formal-conjectures DeanCycles.lean (no formal proof of any case); MathWorld; arXiv 2601.13552,
2605.02731, 2511.03085, 1904.08126; Botsford Zenodo records (via MathWorld). Mathlib: walks, paths,
`IsCycle`, `Walk.take/drop`; no cycle-length-mod-k results, no longest-path lemma of this form.
No Lean proof of any case of Dean's conjecture was found.

## New or known

Known mathematics throughout (the ≡ 2 (mod k) statement is weaker than Gao–Huo–Liu–Ma; the long
cycle lemma is classical). New only as Lean proofs in the formal-conjectures statement shape.
