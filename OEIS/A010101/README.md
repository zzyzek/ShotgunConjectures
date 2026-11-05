# OEIS A010101: a(10) ≤ 116 (upper bound improved from 117)

**Source.** OEIS [A010101](https://oeis.org/A010101), "Maximal size of binary code of length n and
asymmetric distance 2" (size of an optimal code correcting one error on the Z-channel). The entry
comment says the next three terms are known to lie in 112–117, 198–210 and 379–410. The same three
problems are N. J. A. Sloane's challenge graphs 1zc.1024, 1zc.2048, 1zc.4096
(<https://oeis.org/A265032/a265032.html>). (OEIS text, CC BY-SA 4.0.)

**Result.** a(10) ≤ 116, so a(10) ∈ [112, 116]. The upper bound 117 (Etzion–Östergård 1998, as quoted)
is improved by one. a(11) and a(12) are not improved (the same method gives exactly 210 and 410).

**Argument.** Let C be a length-10 code, a_w its number of words of weight w. Two words conflict when
max(N(x,y), N(y,x)) ≤ 1, N(x,y) = #{i : x_i = 1, y_i = 0}. Nine inequalities, each a double count of C
against cliques or subcubes, hold for every code:

| # | inequality | reason | multiplier |
|---|---|---|---|
| 1 | a_9 + 2 a_8 ≤ 10 | a weight-9 word and the 9 weight-8 words below it pairwise conflict; sum over the 10 weight-9 words | 1/10 |
| 2 | a_2 ≤ 5 | weight-2 words of C are disjoint pairs | 2/5 |
| 3 | a_8 ≤ 5 | complement of 2 | 4/5 |
| 4 | a_2 + a_3 ≤ 17 | fact F1 | 1/5 |
| 5 | a_3 + a_4 ≤ 35 | fact F2 | 1/5 |
| 6 | a_6 + a_7 ≤ 35 | complement of 5 | 1 |
| 7 | 45 a_0 + 36 a_1 ≤ 45 | in each of the 45 subcubes of dimension 8 through 0, words of weight ≤ 1 pairwise conflict | 1/45 |
| 8 | Σ_{w=1..5} w a_w ≤ 310 | for each coordinate i, words with x_i = 1 form a 9-cube in which weights 1..5 become 0..4; fact F3 there; sum over i | 1/5 |
| 9 | 9 a_9 + 10 a_10 ≤ 10 | in those 9-cubes, words of global weight 9, 10 pairwise conflict | 1/10 |

With the multipliers every a_w has total coefficient exactly 1 and the right-hand sides sum to
582/5 = 116.4, so |C| ≤ 116.

Facts (all at the stated length, for every code):
- **F1:** weights 2..3 at length 10 hold at most 17 words. Hand proof: weight-2 words form a matching M,
  weight-3 words a triangle packing of K_10 avoiding M; a packing has at most 13 triangles, and a
  13-triangle packing leaves 6 edges with odd degree everywhere, hence a vertex of degree 3, impossible
  if the leave contains a perfect matching; so |M| = 5 forces ≤ 12 triangles.
- **F2:** weights 3..4 at length 10 hold at most 35 words.
- **F3:** weights 0..4 at length 9 hold at most 31 words.

**Evidence.**
- `certificate/certificate_n10.json`: the nine rows and rational multipliers (`zc_certify.py` checks the
  bound exactly in rational arithmetic: 582/5).
- F1: hand proof above; HiGHS 1.15.1 and SCIP both find the maximum 17; CaDiCaL: UNSAT for 18 words.
- F2, F3: proved optimal (35, 31) by two independent branch-and-bound solvers, HiGHS 1.15.1
  (`zc_layers.py`) and SCIP via PySCIPOpt (`zc_scip.py`, clique model for F2: 1215 s; F3: 36 s).
- How the bound was found: `zc_layers.py`, `zc_interval.py`, `zc_recursive.py`, `zc_fixpoint.py`
  (layer LP with averaged clique rows, exact window maxima, and interval rows: every interval of the
  Boolean lattice is a smaller Z-channel cube). `small_windows.json`, `windows_n10_known.json`: the window
  maxima used. `zc.py` rebuilds the Z-channel graphs and matches Sloane's DIMACS files for n = 9..12.
- Lower bounds: local search (`ils.c`) reaches the known 112, but not the records at n = 11, 12.
- Scripts are copies from the working project; they read and write `runs/` (here: this directory).
- `LITERATURE.md`: status of all of Sloane's independent-set challenges (2026-11-04).

**Not verified:** no Lean proof; F2 and F3 rest on two branch-and-bound solvers agreeing (no
machine-checkable certificate).

**Route to a Lean proof.** (1) Definitions and the nine counting inequalities (double counting over
cliques, subcubes and intervals; an interval of the Boolean lattice is a cube of smaller length with the
same conflict relation); the final combination is linear arithmetic with the multipliers above.
(2) F1 and F2 follow from the interval LP recursion starting from exact window maxima at lengths ≤ 6
(checked: the recursion gives exactly 17 and 35, and every window at length 8): a chain of small
rational LP certificates, each justified by the counting lemmas, plus kernel-checked base cases
(at most 64 vertices). (3) F3 reduces to "weights 2..4 at length 9 hold at most 30" (words of weight
≤ 1 pairwise conflict); the recursion gives only 31 there. The case without weight-2 words is
LP-certified (30); a plain branch-and-bound certificate for the rest is too large for the kernel
(over 360 000 nodes unfinished). The likely route is symmetry: the weight-2 words form a matching on
9 points (≤ 4 pairs) and the weight-3 words a linear triple packing, with few configurations up to
coordinate permutation; with one weight-2 pair fixed the strengthened LP is 31.33 against the 31 needed,
so each configuration should close with a small certificate, plus one Lean lemma that permuting
coordinates preserves codes.

**Review level.** `rechecked` (the bound's certificate is exact; three finite facts by two solvers,
F1 also by hand).
**Prior art.** Checked 2026-11-04: OEIS A010101 and Sloane's page give 112–117; the literature since
1998 (Etzion–Östergård; heuristic searches to 2015; a 2026 open-problem proposal citing 117) shows no
better upper bound. Not checked against every coding-theory table.
