# AMR egres-63: minimum k-way cut in hypergraphs for fixed k

**Source.** Egres Open (Egerváry Research Group problem list, http://lemon.cs.elte.hu/egres/open/, Wayback 2024 snapshot), listed at https://amathr.org/problems/. Paraphrase: give a polynomial algorithm for minimum k-way cut in capacitated hypergraphs for fixed k ≥ 4 (k = 2 and k = 3 were known: k = 3 by M. Xiao).

**Reading.** "Capacitated" means non-negative hyperedge costs; a k-way cut is a set of hyperedges whose removal leaves at least k components.

**Result.** Solved (yes). For every fixed k there is a deterministic polynomial algorithm, running in n^O(k)·m time (n vertices, m hyperedges), for non-negative hyperedge costs.

**Argument.** Not reproduced (literature result). Chandrasekaran and Chekuri recover the parts of an optimal k-partition from minimum (S,T)-terminal cuts over polynomially many terminal choices, by divide and conquer. Earlier, Chandrasekaran, Xu and Yu gave a randomized polynomial algorithm (random contraction of hyperedges).

**Evidence.** Citation only; no Lean (an algorithmic complexity result). Outside Lean: the cited theorem.

**Review level.** `agent` (abstract and statements read; proof not re-derived).

**Prior art.** Verdict `known`.
- K. Chandrasekaran, C. Chekuri, *Hypergraph k-cut for fixed k in deterministic polynomial time*, FOCS 2020; Math. Oper. Res. 47 (2022) 3380-3399, https://doi.org/10.1287/moor.2021.1250, arXiv:2009.12442 (abstract read 2026-11-06).
- K. Chandrasekaran, C. Xu, X. Yu, *Hypergraph k-cut in randomized polynomial time*, SODA 2018; Math. Program. 186 (2021) 85-113.
Searched: web, arXiv, google-deepmind/formal-conjectures (local clone 2026-11-06; nothing on this) (2026-11-06).
