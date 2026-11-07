# AMR topp-67: fair partitions of convex polygons into n convex pieces

**Source.** The Open Problems Project, Problem 67 (Demaine, Mitchell, O'Rourke; https://topp.openproblem.net/p67), listed at https://amathr.org/problems/. Paraphrase: can every convex polygon be partitioned into n convex pieces that all have the same area and the same perimeter, for every n? (Nandakumar and Ramana Rao.)

**Result.** Yes, for every n ≥ 2. The TOPP page (read 2026-11-06) still lists the problem as open, with n = 2, 3, 4 and prime powers n = p^k settled (Nandakumar-Ramana Rao; Bárány-Blagojević-Szűcs; Aronov-Hubard and Karasev 2010). The secondary questions on the page (deciding feasibility for a given polygon, minimising total cut length, higher dimensions for non-prime-power n) are not addressed here.

**Argument.** Not reproduced (literature result). Akopyan, Avvakumov and Karasev prove that every convex body in the plane, in particular every convex polygon, has a partition into m convex parts of equal area and equal perimeter for every integer m ≥ 2. The prime-power case uses an equivariant-topology (configuration space / Voronoi) argument; they extend it to all m by an inductive cutting scheme with a degree computation.

**Evidence.** Citation only; no Lean (needs equivariant topology). Outside Lean: the cited theorem.

**Review level.** `agent` (abstract read; proof not re-derived).

**Prior art.** Verdict `known`. A. Akopyan, S. Avvakumov, R. Karasev, *Convex fair partitions into an arbitrary number of pieces*, arXiv:1804.03057 (v14, 2026-03-20), Adv. Math. 493 (2026), doi:10.1016/j.aim.2026.110927 (abstract read 2026-11-06). Searched: web, arXiv, TOPP page, Open Problem Garden, google-deepmind/formal-conjectures (local clone 2026-11-06) (2026-11-06).
