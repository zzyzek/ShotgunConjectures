# CFG F16: the thrackle conjecture for small n

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section F16. A thrackle is a drawing of a graph in the plane in which every pair of edges meets
exactly once, either at a common endpoint or at a proper crossing. Conway's thrackle conjecture
says a thrackle on n vertices has at most n edges. The book notes experimental evidence near
n = 10 and asks whether there is at least a proof for small n.

**Result.** Known. The thrackle conjecture holds for every graph with at most 12 vertices
(J. Pammer 2014, by enumerating path-thrackles). The bound n <= 11 was used earlier as a known
fact (Goddyn and Xu 2017). The general conjecture is open.

**Argument.** Computer enumeration in the cited thesis; not re-derived here.

**Evidence.** Citation only. Lean status `none`: thrackles are topological drawings, and a
formal check would need a combinatorial encoding (rotation systems plus crossing data) and an
enumeration of the size done by Pammer, out of reach for core Lean `decide`.

**Review level.** `agent` (citation read through the GD 2019 paper; the thesis itself was not read).

**Prior art.** Checked 2026-11-06.
- O. Aichholzer, L. Kleist, B. Klemz, F. Schröder, B. Vogtenhuber, *On the edge-vertex ratio of
  maximal thrackles*, GD 2019, arXiv:1908.08857, introduction: the conjecture "has been improved
  to n<=12 in the course of enumerating all path-thrackles", citing Pammer.
- J. Pammer, *Rotation systems and good drawings*, MSc thesis, TU Graz, 2014.
- L. Goddyn, Y. Xu, *On the bounds of Conway's thrackles*, Discrete Comput. Geom. 58 (2017) 410-416
  (use n <= 11).
- G. Misère, Y. Nikolayevsky, *Thrackles containing a standard musquash*, arXiv:1601.05562 (call
  n <= 11 folklore).
- R. Fulek, J. Pach, *A computational approach to Conway's thrackle conjecture*, Comput. Geom.
  44 (2011), arXiv:1002.3904: verify the conjecture for bipartite graphs on at most 10 vertices
  and prove at most 1.428n edges.
- google-deepmind/formal-conjectures tree HEAD 2026-11-06: no thrackle file.
