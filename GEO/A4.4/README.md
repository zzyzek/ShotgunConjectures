# Croft–Falconer–Guy A4: billiards in the regular tetrahedron — every periodic orbit has even period

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991), section A4
(paraphrased): Steinhaus asked whether every polyhedron has a periodic billiard orbit. Conway showed circuits
exist in all tetrahedra and said the regular tetrahedron has a continuous family of periodic quadrangles, two
periodic hexagons, and no other orbits with fewer than eight bounces. Are there periodic orbits with arbitrarily
many bounces, and do they all have an even number of bounces?

**Reading.** Billiard trajectories avoid edges and vertices; a periodic orbit returns to its starting point with
its starting direction after k bounces (k minimal).

**Result.** Partial.
1. (New, proved.) In the regular tetrahedron every periodic billiard orbit has an even number of bounces.
2. (New, proved.) Every periodic orbit is isolated: there is no continuous (parallel) family of periodic orbits
   of any period. This contradicts the "continuous family of periodic quadrangles" as reported in the book;
   there are exactly three periodic quadrangles (each hitting the four faces once, one per cyclic order up to
   reversal).
3. (Computation, exact.) Primitive periodic orbits exist with k = 4, 6, 12, 14, 16, 18, 20 bounces and none with
   k = 2, 8, 10 (exhaustive for k ≤ 10 by the exact search; for 12 ≤ k ≤ 20 a floating-point screen whose hits
   were all verified exactly). Numbers of primitive cyclic face words (rotations of words starting with face 0):
   k = 4: 6, 6: 20, 12: 80, 14: 36, 16: 12, 18: 16, 20: 72. This supports "arbitrarily many bounces"
   but does not prove it. Steinhaus's question for all polyhedra stays open.

**Argument.** Faces: n_f · x = 1 with n_f = −V_f, V_f the vertices (±1,±1,±1) with an even number of minus
signs. The reflection in face f is x ↦ L_f x + t_f with 3L_f = 3I − 2 n_f n_fᵀ. A periodic orbit with cyclic face
word w = f_1 … f_k unfolds to a line ℓ with G(ℓ) = ℓ, G = σ_{f_1} ∘ … ∘ σ_{f_k}, preserving the direction u, so
L_w u = u for the linear part L_w = L_{f_1}⋯L_{f_k}.
- Mod 3: 3L_f ≡ n_f n_fᵀ, and n_f · n_g = −1 for f ≠ g, so 3^k L_w ≡ (−1)^{k−1} n_{f_1} n_{f_k}ᵀ (mod 3) and
  trace(3^k L_w) ≡ (−1)^k (mod 3) when f_k ≠ f_1. Hence trace(L_w) ≠ 1 and L_w ≠ I (both give a trace of
  3^k L_w divisible by 3).
- Odd k: L_w is orthogonal with det −1 and eigenvalue 1, so its eigenvalues are 1, 1, −1 and its trace is 1;
  impossible. So k is even.
- Even k: L_w is a rotation ≠ I fixing u, so G is a screw motion whose only invariant line parallel to u is its
  axis. Hence the orbit with word w is unique, i.e. isolated, and orbits are found by testing the axis of G_w.

**Evidence.**
- Lean (core): [`A4_4.lean`](A4_4.lean). `trace_not_dvd`: for every cyclically reduced word, the trace of
  P_w = (3L_{f_1})⋯(3L_{f_k}) (an integer matrix) is not divisible by 3; `not_identity_not_reflection`:
  trace(P_w) ≠ 3·3^k and ≠ 3^k. Kernel `decide` on the finite step tables plus an induction.
  `tools/leancheck.sh`: OK, no warnings, axioms propext, Classical.choice, Quot.sound.
- [`certificate/orbits.py`](certificate/orbits.py) (exact search via screw axes, k ≤ 10),
  [`certificate/orbits.c`](certificate/orbits.c) (floating screen, k ≤ 20),
  [`certificate/verify_words.py`](certificate/verify_words.py) (exact Fraction verification: all 960 screened
  words verified), `certificate/cand_*.txt` (the words), [`certificate/search.c`](certificate/search.c)
  (no odd word up to k = 15 has a reflection as linear part, a check of the mod-3 lemma).
- Outside Lean: the unfolding argument (linear algebra of isometries) and the orbit searches.

**Review level.** `lean-proof` for the mod-3 lemma; `rechecked` for the geometric step and the data.

**Prior art.** Checked 2026-11-07: Bédaride, Forum Geom. 8 (2008) (stability of the 4-periodic word in
tetrahedra; notes a counterexample to Conway's claim that abcd is periodic in all tetrahedra), Bédaride–Rao,
Proc. AMS (regular simplices: periodic orbits of periods n+1 and 2n), Stenman 1975 (period 4), web searches on
odd periods in the regular tetrahedron (nothing found), formal-conjectures (nothing). The parity and isolation
statements were not found in print.
