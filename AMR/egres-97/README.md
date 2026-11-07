# AMR egres-97: well-balanced orientations of hypergraphs

**Source.** Egres Open (Egerváry Research Group problem list, http://lemon.cs.elte.hu/egres/open/Well-balanced_orientations_of_hypergraphs; the page is gone and the 2022-2024 Wayback snapshots return 404), listed at https://amathr.org/problems/. The title appears both in the solved and in the open list of the archived problem list. Paraphrase (from the title and from the citing paper): extend Nash-Williams' well-balanced orientation theorem (every graph has an orientation with λ_D(u, v) ≥ ⌊λ_G(u, v)/2⌋ for all u, v) to hypergraphs, or decide which hypergraphs have such an orientation.

**Reading.** A hypergraph is oriented by choosing a head in each hyperedge (the other vertices are tails; Frank-Király-Király). The page text is lost; the reading follows Hörsch and Szigeti, who cite this page as the source of the question.

**Result.** Answered negatively. No theorem of Nash-Williams type holds: some hypergraphs have no well-balanced orientation, and deciding whether a given hypergraph has one is NP-complete.

**Argument.**
- Small example (ours, re-derived): H on {a, b, c} with two copies of the hyperedge {a, b, c}. Every pair u, v lies in both hyperedges, so λ_H(u, v) = 2, and a well-balanced orientation needs λ_D(u, v) ≥ 1 for every ordered pair. A vertex can only be entered through a hyperedge whose head it is; two heads among three vertices leave some vertex v with no entering hyperedge, so λ_D(u, v) = 0.
- NP-completeness: Hörsch and Szigeti, Theorem 6 (reduction from a satisfiability-type problem; not re-derived).

**Evidence.** Citation plus the example above; no Lean. Outside Lean: the example (three lines) and the cited NP-completeness proof.

**Review level.** `rechecked` for the example, `agent` for the NP-completeness.

**Prior art.** Verdict `known`. F. Hörsch, Z. Szigeti, *Steiner connectivity problems in hypergraphs*, arXiv:2211.02525 (v2, 2023), Theorem 6 "WBOH is NP-complete"; they write that the failure of Nash-Williams' theorem for hypergraphs is easy to see and cite the Egres page as [5] (full text read 2026-11-06). Searched: web, arXiv, cached Egres list (scan repo artifacts), google-deepmind/formal-conjectures (local clone 2026-11-06) (2026-11-06).
