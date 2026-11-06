# AIM matrix spectra workshop, energy Q1 and Q2: edge deletion changes the energy by exactly 2

**Source.** AIM workshop "Spectra of families of matrices described by graphs, digraphs and sign patterns" (Oct
2006), report "Open Questions" by I.-J. Kim and A. W. Wehe, section 3 (Energy of graphs). E(G) is the sum of the
absolute values of the adjacency eigenvalues. Q1: if e is an edge of a connected graph G with E(G) = E(G \ e) + 2,
must G = K2? Q2: is there a graph G with E(G \ e) = E(G) + 2 for some edge e?

**Result.** Q1: yes (known: Day and So 2007). Q2: no; for every graph G and edge e, E(G \ e) < E(G) + 2, and in fact
E(G \ e) = E(G) + 2 would force E(G \ e) <= E(G).

**Argument.** For a real symmetric X, E(X) = sum |lambda_i(X)| = max tr(W X) over symmetric W with operator norm
<= 1, attained at W = sign(X) (write X = sum lambda_i v_i v_i^T; then tr(W X) = sum lambda_i <v_i, W v_i> and
|<v_i, W v_i>| <= 1). Let A = A(G), e = uv, B = e_u e_v^T + e_v e_u^T, so A(G \ e) = A - B and E(B) = 2.

- *Q2.* Take W = sign(A - B). Then E(G \ e) = tr(W A) - 2 W_uv <= E(G) - 2 W_uv <= E(G) + 2. Equality needs
  W_uv = -1. Since (W^2)_uu = sum_j W_uj^2 <= 1, row u of W (and likewise row v) is zero except W_uv = W_vu = -1.
  Then in tr(W (A - B)) every term touching u or v vanishes (the only nonzero W entries there sit on the deleted
  edge), so E(G \ e) = tr(W_R A_R) with R = V \ {u, v}, A_R the adjacency matrix of the induced subgraph G[R] and
  W_R a contraction: E(G \ e) <= E(G[R]). Extending sign(A_R) by zeros gives a contraction W' with
  tr(W' A) = E(G[R]), so E(G[R]) <= E(G). Hence E(G \ e) <= E(G) < E(G) + 2, a contradiction.
- *Q1.* The same computation with W = sign(A) gives E(G) <= E(G \ e) + 2 with equality only if W_uv = 1 and rows u, v
  of W vanish elsewhere; Day and So (ELA 16, 2007) show that equality holds iff e is a component of G, so for
  connected G, G = K2.

**Evidence.**
- [`certificate/energy_q.py`](certificate/energy_q.py): over all graphs on at most 7 vertices (networkx atlas) and all
  edges, max(E(G \ e) - E(G)) = 1.0465 and, for connected G other than K2, max(E(G) - E(G \ e)) = 1.8524.
- Lean (Mathlib): [`aimmatrix_en2_mathlib.lean`](aimmatrix_en2_mathlib.lean), namespace `AimEnergy`. Main theorem
  `aim_energy_Q2 : G.Adj u v → energyG (G.deleteEdges {s(u, v)}) < energyG G + 2` for every simple graph G on a
  finite vertex type, with `energyG G` the sum of |eigenvalues| of `G.adjMatrix ℝ`; matrix form `energy_delete_lt`.
  Route: `trace_le`, `sgn_contr`, `trace_sgn`, `col_sq_le`, `trace_mul_Bm` (the argument above, with the
  zero-extension step replaced by the contraction W + (E_uv + E_vu)). Check: `tools/leancheck-mathlib.sh`, exit 0,
  no warnings; axioms of every theorem propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- Outside Lean: Q1 (cited theorem of Day and So, not reproved in Lean).

**Review level.** `lean-proof` for Q2; Q1 cited.

**Prior art.** Checked 2026-11-06. Q1: J. Day, W. So, Singular value inequality and graph energy change, Electron.
J. Linear Algebra 16 (2007) 291-299: E(G) <= E(G - e) + 2 with equality iff e is a component of G (as quoted in
MATCH 96 (2026) 907-915). Its abstract also announces a bound for the energy change on deleting the edges of a
nonsingular induced subgraph H that is "never sharp", which for H = K2 is presumably E(G - e) < E(G) + 2, i.e. Q2;
the full text could not be retrieved here (publisher pages behind a bot check), so Q2 is recorded as partly known.
Not in google-deepmind/formal-conjectures (clone of 2026-11-06).
