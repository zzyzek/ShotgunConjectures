# GEO C10.2: the plane can be tiled with exactly one square of each positive rational side

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991),
Section C10 (squares tiling the plane). Question: can the plane be tiled using exactly one
square of each positive rational side?

**Result.** Yes. F. V. Henle and J. M. Henle, *Squaring the plane*, Amer. Math. Monthly 115
(2008) 3–12, tile the plane with one square of each positive integer side (Golomb's
heterogeneous tiling conjecture). The authors note that their algorithm can easily be used to
tile the plane with one square of every rational side (squaring.net, *Squaring the Plane I*,
quoting the Henles).

**Argument (re-derived).** The Henle construction alternates two steps.
1. *Fill.* Place the next unused size at a fixed corner of the current tiled region. For
   integers this is the smallest unused size. For the rationals, fix an enumeration
   q_1, q_2, … of Q_{>0} and use the first unused q_i.
2. *Puff up.* Extend the current region (an L-shape) to a perfect tiled rectangle. The new
   squares have sizes that are integer combinations of sizes already placed, each larger than
   every size used so far.

Step 2 stays valid over Q. Integer combinations of rationals are rational. Only finitely many
sizes are in use at any stage, so sizes above the current maximum are unused, and the sizes in
one puff-up step are distinct because they increase strictly. Step 1 uses every q_i
eventually, because after the i-th fill step q_1..q_i are all placed. The plane-covering part
of the Henle proof (the rectangles grow in all four directions in turn) does not depend on
which size step 1 inserts. So every positive rational appears exactly once and the union is
the plane.

**Evidence.** Literature. No Lean: the statement is about an infinite geometric construction,
and core Lean has no plane-tiling library. Outside Lean: everything (published construction,
plus the re-derivation above of the change from integers to rationals).

**Review level.** `rechecked` (argument re-derived from the published construction).

**Prior art.** Checked 2026-11-06: Henle & Henle 2008; squaring.net page *Squaring the Plane I*
(quotes the rational remark and says the half-plane and quarter-plane versions are open);
web search; google-deepmind/formal-conjectures (HEAD 2026-11-05, no entry).
