# Croft–Falconer–Guy G9: two sets always meeting in exactly n points — odd n is impossible for curve-like sets

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991), section G9
(paraphrased): Steinhaus asked for two plane sets that meet in exactly one point however they are placed
(Sierpiński: yes, using the axiom of choice). For sets always meeting in exactly n points, n even has a simple
example: parallel lines at unit spacing and a circle of radius n/4. Are there such simple examples for odd n?

**Reading.** "Placed" = moved by a rigid motion g (orientation-preserving; the result also holds with
reflections). N(g) = |A ∩ gB|. "Simple" is read as: both sets are curve-like (locally finite embedded graphs).

**Result.** Partial (negative for the natural class). Let A be a locally finite union of straight lines and B a
compact embedded graph with finitely many C¹ edges. If N(g) = n for every rigid motion g, then n is even.
So the even-n example (lines and a circle, or lines and any closed curve of constant width n/2) has no odd-n
analogue with A a family of lines and B a finite union of arcs; odd n needs a set that is not a finite union
of arcs. The same argument (sketched below) applies when A is any locally finite embedded C² graph.
An explicit odd-n example (simple or Borel) remains open.

**Argument.** (1) Every vertex of B has even degree. Suppose p is a vertex of odd degree (an endpoint has degree
1). Choose g₀ with g₀(p) on a line λ of A, all edges of g₀B at g₀(p) transverse to λ, and no other vertex of g₀B
on A. Moving g across the wall W_p = {g : g(p) ∈ A} changes the number of intersections near g(p) by
deg(p) − 2k for some k, an odd number. Tangencies elsewhere change N by 0 or ±2. Another vertex p′ can lie on A
for all g in an open subset of W_p only if A contains, for each a in an interval of λ, an arc of the circle of
radius |p − p′| around a, i.e. a set with interior; A has none. So such g₀ exist, N mod 2 changes across W_p,
and N is not constant. (2) With all degrees even, B is a mod-2 1-cycle; being compact in ℝ² it bounds a compact
2-chain D (mod 2). For g with gB transverse to every line of A (generic g), each line λ meets gB = ∂(gD) in an
even number of points (λ ∩ gD is a finite union of segments whose endpoints are exactly λ ∩ gB). Summing over
the finitely many lines meeting gB, N(g) is even. Since N is constant, n is even.
General A (sketch): the wall argument works for vertices of A as well (use g⁻¹), with the extra case of an edge
of A that is a circle arc centred at a vertex of A, which one avoids by choosing the crossing point on another
edge; step (2) uses that a locally finite even-degree graph meets a compact mod-2 boundary evenly.

**Evidence.** Paper argument only. Lean: none (plane topology and transversality are far from core Lean).
Outside Lean: everything.

**Review level.** `agent`.

**Prior art.** Checked 2026-11-07: web searches (Steinhaus two-set problem, odd n), the Steinhaus lattice problem
literature (Jackson–Mauldin 2002; "Measurable Steinhaus sets do not exist for finite sets or the integers in the
plane", arXiv 1604.06454; Gao–Miller–Weiss), formal-conjectures (nothing). No statement of this parity
obstruction was found; it may be folklore.
