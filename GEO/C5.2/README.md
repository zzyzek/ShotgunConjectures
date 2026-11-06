# CFG C5: incomparable tilings cannot have all tiles close to squares

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section C5 (Tiling with incomparable rectangles and cuboids). Two rectangles are incomparable if
neither fits inside the other with sides parallel: with dimensions a1 x a2 and b1 x b2 suitably
labelled, a1 < b1 <= b2 < a2. Paraphrase of the question: for tilings of a rectangle with many
pairwise incomparable rectangles, can every tile have aspect ratio arbitrarily close to 1?

**Reading.** "Fit inside" allows rotation (the book's labelling with sorted sides). The answer
below holds also if rotation is not allowed (with constant sqrt 2 in place of 2).

**Result.** No. In every tiling of a rectangle by at least two pairwise incomparable rectangles,
some tile has aspect ratio (long side / short side) at least 2.

**Argument.** Write each tile with short side s and long side l, and let rho be the largest
aspect ratio. Suppose rho < 2.

1. *All sides lie in [m, rho m) for m the least short side.* Two tiles with equal short side are
   comparable, and if s_i < s_j then incomparability forces l_i > l_j. So the tile with the
   least short side m has the largest long side, which is at most rho m. Hence every side
   (width or height) of every tile lies in [m, rho m], and any side is less than twice any other
   side (rho m < 2m).
2. *Equal sides make tiles comparable.* If two tiles share a width (or a height, or a width of one
   equals a height of the other), the one with the shorter other side fits in the other.
3. *Two tiles share a side length.* Let A = [0,w] x [0,h] be the tile at the lower left corner of
   the tiled rectangle [0,W] x [0,H]. Since there are at least two tiles, w < W or h < H.
   - If w = W: the tiles meeting the segment y = h + (small), 0 < x < W, partition [0,W] into widths
     each at least m > W/2 (W = w <= rho m < 2m), so there is one such tile and its width is
     w. Symmetrically if h = H.
   - Otherwise let T be the tile just right of A's right side near its top corner (it contains
     points (w + d, h - d) for small d > 0), with vertical extent [y_b, y_t], y_b < h <= y_t.
     - If y_t = h: below T on the vertical line x = w + d lie tiles filling [0, y_b], each of
       height at least m. But y_b = h - height(T) <= rho m - m < m, so y_b = 0 and
       height(T) = h = height(A).
     - If y_t > h: T contains points (w + d, h + d). Let U be the tile just above A near A's
       right end (containing (w - d, h + d)). U and T have disjoint interiors, so U's right side
       is x = w. Its left side x_l = w - width(U) <= rho m - m < m, while the tiles left of U on
       the line y = h + d fill [0, x_l] with widths at least m; so x_l = 0 and width(U) = w =
       width(A).
   In every case two distinct tiles have a common side length, so by step 2 they are comparable,
   a contradiction.

Without rotation (incomparable meaning w_i < w_j forces h_i > h_j, and conversely), step 1 gives
(h_max / h_min)(w_max / w_min) <= rho^2, and step 3 needs only h_max < 2 h_min and
w_max < 2 w_min, so rho >= sqrt 2 for every such tiling.

The bound is about the existence question only; we did not determine the least possible maximum
aspect ratio (the 13 x 22 tiling of Yao, Reingold and Sands has a 1 x 18 tile).

**Evidence.** The argument above (elementary plane geometry). No Lean: formalising "the tile just
right of A near its corner" for a general finite tiling is the whole difficulty and was not done
in this round. Outside Lean: the whole argument.

**Review level.** `agent` (derived once; each step re-read).

**Prior art.** Checked 2026-11-06: the C5 text in the book; web searches on incomparable rectangle
tilings with near-square tiles; G. M. Georgiou, arXiv:2609.19536 (2026), which settles the other C5
question (27 is the least side of a square tileable by incomparable integer rectangles) and does not
treat aspect ratios; MathWorld "Incomparable Rectangles". No statement of this bound found.
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (clones of 2026-11-06,
grep for "incomparable").
