# BMP 1.5 Problem 4: a nonconvex plane body tiling by translates tiles by a lattice

**Source.** P. Brass, W. Moser, J. Pach, *Research Problems in Discrete Geometry*, Springer 2005,
Section 1.5, Problem 4 (Grünbaum–Shephard): if a nonconvex plane body C tiles the plane by
translates, does it tile by a lattice? The authors add that even periodicity is not known.

**Reading.** BMP Chapter 0 defines a body as a set homeomorphic to a ball; in the plane, a closed
topological disk. Under that definition the problem is answered.

**Result.** Yes for bodies in BMP's sense. Girault-Beauquier and Nivat (1991, with boundary
conditions; Beauquier–Nivat for polyominoes, Discrete Comput. Geom. 6 (1991) 575–592) and
R. Kenyon, *Rigidity of planar tilings*, Invent. Math. 107 (1992) 637–651 (erratum 112 (1993) 223)
proved that a closed topological disk tiling the plane by translations has boundary split into 4
or 6 arcs matched in opposite pairs by translations (pseudo-square or pseudo-hexagon), which gives
a lattice tiling. For general compact tiles (disconnected or with holes) the periodic tiling
question in R^2 is open: R. Greenfeld, *Translational tilings: structured or wild?*,
arXiv:2509.25576 (2025), Section 7, Question 7.4.

**Evidence.** Citation. The periodic statement for topological disks is confirmed from the
Greenfeld survey; the lattice form is as Kenyon's theorem is cited in secondary sources
(Kenyon's paper itself not read here). No Lean.

**Review level.** `agent`.

**Prior art.** Searched web, arXiv (Greenfeld survey), google-deepmind/formal-conjectures
(Fuglede, spectral sets only). 2026-11-07.
