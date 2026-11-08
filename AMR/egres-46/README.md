# Egres Open: gonality under edge subdivisions

**Source.** Egres Open (Egervary Research Group), problem "Gonality under edge subdivisions" (Wayback 2024
snapshot; listed at amathr.org/problems). Paraphrase: how does the divisorial gonality dgon change when every
edge is subdivided k times? Is the ratio bounded? Can it change for odd k?

**Reading.** sigma_k(G): every edge replaced by a path of k edges (k - 1 new vertices). "Subdivided k times" may
mean sigma_k or sigma_{k+1}; this changes the parity in the third question.

**Result (partial; known parts by others).**
- Ratio: bounded. J. van Dobben de Bruyn, H. Smit, M. van der Wegen, *Discrete and metric divisorial gonality can
  be different*, J. Combin. Theory Ser. A 189 (2022) 105619 (arXiv:2106.12568): dgon(Gamma(G)) = min_k
  dgon(sigma_k G) and dgon_r(G) <= 2 dgon_r(Gamma(G)) - r, so 1 <= dgon(G)/dgon(sigma_k G) <= 2; their examples
  give ratios up to 6/5; the best constant is open (their Section 6).
- Change: yes for sigma_2 (tricycle graphs: dgon 6, dgon(sigma_2) = 5), hence for every even k in the sigma_k
  reading, and for k = 1 in the "one inserted vertex" reading. Whether dgon(sigma_k G) < dgon(G) for some odd k
  is listed as open in the same paper.
- Our computation (new evidence, no counterexample): exhaustive divisor search (`certificate/dgon.c`, Dhar
  burning) gives dgon(sigma_k T) = 6, 5, 6, 5, 6 for k = 1..5 on the minimal tricycle multigraph T_m and
  6, 5, 6 for k = 1..3 on the simple tricycle T_ms (paper's values for k = 1, 2 reproduced); in a family of
  generalised tricycles (cycle lengths 2-4, transition paths 1-3, spokes 1-2; `certificate/family.out`) many
  drop at k = 2 and none at k = 3; among all 994 connected graphs on <= 7 vertices with dgon <= 5 none drops at
  k = 3 (`certificate/atlas.out`).

**Evidence.** No Lean. Outside Lean: the cited theorems and the C search (exhaustive over effective divisors of
each degree; rank >= 1 tested by v-reduced divisors).

**Review level.** agent (citations read 2026-11-08); computation rechecked against the paper's k = 1, 2 values.

**Prior art.** arXiv:2106.12568 (JCTA 2022) Sections 1 and 6; web search 2026-11-08 found no later answer to
the odd-k question.
