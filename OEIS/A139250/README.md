# OEIS A139250: holes of the toothpick structure are rectangles (side lengths still open)

**Source.** OEIS [A139250](https://oeis.org/A139250), conjecture listed on the OEIS wiki
(Talk:Conjectures/List): "Consider the rectangles in the sieve (including the squares). The area
of each rectangle (A = b*c) and the edges (b and c) are powers of 2, but at least one of the edges
(b or c) is <= 2." (OEIS text, CC BY-SA 4.0.)

**Reading.** Unit length = half a toothpick. A toothpick is a closed axis-parallel segment of
length 2 with lattice centre c and endpoints c ± e (e a unit vector); it covers the three lattice
points c - e, c, c + e. Stage 1 is the vertical toothpick centred at the origin. At stage n ≥ 2,
for every toothpick placed at stage n - 1 and every endpoint p of it, p is *exposed* if no other
toothpick placed so far contains p; a toothpick perpendicular to the parent and centred at p is
added at every exposed p. (This is the OEIS rule "an end is exposed if it does not touch the end
or the middle of another toothpick"; `certificate/sim.py` and `certificate/check_lemmas.py`
reproduce A139250.) L is the union of all toothpicks over all stages (the "sieve"). A *hole* (a
"rectangle in the sieve") is a bounded connected component of R² \ L. Every point lies inside the
box |x| ≤ 2^(k-1) - 1, |y| ≤ 2^(k-1) for large k, and that box has its whole boundary in L from
stage 2^k on, so holes are exactly the bounded faces seen inside these boxes.

**Result.** Partial.
- New proof (statement known): every hole is the open rectangle (x0, x0+w) × (y0, y0+h) with
  integers w, h ≥ 1, its whole boundary in L and no point of L inside (Theorem 1). Applegate, Pol
  and Sloane state that all internal regions are rectangles ("We omit the proof"); the proof below
  is local and uses no self-similarity.
- New: each side of a hole is covered by collinear toothpicks of one single stage, and every such
  toothpick centred inside the side has its parent outside the hole (Corollary 2).
- Open here: the side lengths are powers of 2 and the shorter side is ≤ 2. Checked to stage 512
  (116496 holes, round r14) and re-checked to stage 256 by `check_lemmas.py`. Shapes seen at
  stage 2^K: 1×2^j for j ≤ K-3 and 2×2^j for j ≤ K-2.

**Argument.**

*Lemma 1 (orientation and parity).* Toothpicks of stage n are vertical iff n is odd. Vertical
toothpicks have centres with x + y even, horizontal ones with x + y odd.
Proof: induction on n. A child is perpendicular to its parent and centred at a parent endpoint
c ± e, which changes the parity of x + y.

*Lemma 2 (no overlap).* No unit segment lies in two toothpicks.
Proof: both unit segments of a toothpick t contain its centre p. Let t be placed at stage n and
let u ≠ t be placed at stage ≤ n with a common unit segment, so u contains p. If u is placed before
stage n, then u is not the parent (the parent is perpendicular and meets t only at p, sharing no
segment), so p was not exposed, a contradiction. If u is placed at stage n, then u ∥ t (Lemma 1);
u ≠ t gives a different centre, and a common unit segment forces the centres to be at distance 1
along the line, which have different parities of x + y, contradicting Lemma 1.

*Lemma 3 (no corners and no dead ends).* For a lattice point p let D(p) be the set of unit
directions d with the segment [p, p+d] in L. Then D(p) is empty, {N, S}, {E, W}, or has at least
3 elements.
Proof: if p is the centre of some toothpick, D(p) contains an opposite pair, and any set with an
opposite pair is in the list. Otherwise every unit segment of L at p lies in a toothpick whose
centre is not p, so p is an endpoint of it. Suppose D(p) is nonempty and let t be a toothpick
ending at p with the smallest stage n. If no other toothpick of stage ≤ n contains p, then p is
exposed after stage n and a toothpick is centred at p at stage n + 1, a contradiction. So some
u ≠ t of stage ≤ n contains p, as an endpoint since p is not a centre, so u has stage n by
minimality. By Lemma 1 u ∥ t, and by Lemma 2 they lie on opposite sides of p, so D(p) contains an
opposite pair.

*Square completion.* Call two edge-adjacent unit cells *joined* if their common edge is not in L.
If a cell a is joined to its horizontal neighbour b and to its vertical neighbour d, let p be the
corner common to a, b, d. Two perpendicular directions at p are missing from D(p). Each set allowed
by Lemma 3 other than ∅ contains one of any two perpendicular directions, so D(p) = ∅ and the
fourth cell at p is joined to b and to d.

*Theorem 1.* Every hole is an open lattice rectangle whose boundary lies in L and whose interior
misses L.
Proof: L is a union of unit lattice segments, so a component of R² \ L is the union of a class of
cells under the joined relation together with the open edges and lattice points between them. Take
a hole and its finite set C of cells. In a row, a *run* is a maximal sequence of consecutive cells
of C, each joined to the next. If one cell of a run R is joined to the cell above it, square
completion applied step by step along R shows that every cell of R is joined to the cell above and
that these cells are joined to each other; so they lie in one run R' of the row above, and the same
argument downwards gives R' = R + (0, 1). Hence C is a stack of equal runs, that is a w × h
rectangle of cells. Its interior edges are not in L, its interior lattice points have D = ∅, and
each boundary edge is in L (otherwise the outside cell would be joined to C).

*Corollary 2 (sides are one-stage chains).* Let p be a lattice point strictly inside a side of a
hole. D(p) contains both side directions and not the inward one. If p is a centre, its toothpick
lies along the side and its parent ends at p from outside. If p is not a centre, the proof of
Lemma 3 gives two parallel toothpicks of the same (smallest) stage ending at p from opposite sides;
they cannot be perpendicular to the side (one would point inward), so they are the two side
toothpicks meeting at p. Walking along the side, consecutive toothpicks therefore have equal stage.

*Toward the size claims (proved lemmas plus a numerically checked decomposition).*
- Mirror lemma (proved). In the full structure no toothpick other than the stage-1 one is centred
  on the x-axis, and the stage-1 and stage-2 toothpicks are the only ones centred on the y-axis; an
  end reaching an axis is reached at the same stage by its mirror image, so it is never exposed.
  Hence the quadrant x, y ≥ 0 evolves as the wall process in which every axis point counts as
  covered, started from the pieces (0,0)-(0,1) and (0,1)-(1,1).
- Seam lemma (proved). Split a wall process by a lattice line ℓ into two half-plane processes that
  treat ℓ as a wall. If for every point of ℓ both sides touch it first at the same stage (or never),
  the joint process is the union of the two, and L carries no segment of ℓ there; a hole meeting ℓ
  is then the union of a boundary room of each side between consecutive touch points.
- Corner decomposition (checked for k = 2..6 by `certificate/decomp_check.py`, not proved). With
  A = 2^(k-1), the quadrant at stage 2^(k+1) is the quadrant at stage 2^k (box [0, A-1] × [0, A],
  sealed, one exposed end at (A, A)), plus the quadrant process restarted at (A, A), plus its mirror
  image in x = A (above the box), plus a *strip process* in x ≥ A - 1, 0 ≤ y ≤ A with walls on all
  three sides started from the half toothpick (A, A)-(A, A-1). The seam y = A has touch points
  (A + 2^i - 1, A) at stage 2^k + 2^(i+1) - 1 from both sides, as the seam lemma needs. The strip of
  height h run 2h stages splits into three copies of the strip of height h/2 (translated, translated,
  flipped) and a fourth block of a new type (lower left), bounded by the sealed line y = h/2 + 1, the
  walls x = 0, y = 0 and the seam x = h/2.

**Evidence.**
- `certificate/check_lemmas.py K`: reproduces A139250(1..20) and checks Lemmas 1-3, Theorem 1 and
  Corollary 2 on the box at stage 2^K; passed for K = 5..8 (29116 holes at K = 8). The lemmas are
  proved above; this is a consistency check of the definitions.
- `certificate/decomp_check.py` (uses `wp.py`, `sim.py`): mirror lemma output, corner decomposition
  and seam profile for k = 2..6, strip blocks for h = 4..32.
- Round-r14 scripts (`open-problems/work/OEIS-A139250/faces.py`, `faces9.py`): side-length claim to
  stage 512.
- Outside Lean: everything (paper proofs of Lemmas 1-3, Theorem 1, Corollary 2, mirror and seam
  lemmas; the decomposition and side lengths only numerically).

**Review level.** `agent` for Theorem 1 and Corollary 2 (paper proof, checked on data to stage
256); side-length claim open.

**Open part, precise obstruction.** The power-of-2 and short-side claims need the boundary-room
profiles of every process type on every pseudo-seam. Three types are identified (quadrant, strip,
lower-left block of the strip); the lower-left block has walls offset by one (it lives in
[0, H] × [0, H+1] under the sealed line y = H + 1 and meets the strip copy at x = H), and its own
recursion, seam profiles and the closure of the type list are not established.

**Prior art.** D. Applegate, O. E. Pol, N. J. A. Sloane, "The toothpick sequence and other
sequences from cellular automata", Congressus Numerantium 206 (2010), arXiv:1004.3036, Section 4:
internal regions are squares and rectangles, proof omitted; nothing on side lengths. No entry in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (checked 2026-11-06, round r14; not
re-searched). The OEIS entry still lists the conjecture (fetched 2026-11-01).
