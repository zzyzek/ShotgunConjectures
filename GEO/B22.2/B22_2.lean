/-
GEO B22.2 (Croft-Falconer-Guy B22, orientation-preserving case).
Checked here: the two finite combinatorial facts of the argument in README.md.
1. `label_cycle`: around a vertex of degree d, edge labels in {0,1,2} (= a, b, c) satisfy
   L (i+1) = L i + 2 (mod 3) (each face is a direct copy, so its sides a, b, c appear in the same
   cyclic order); if the labels close up after d steps (L d = L 0) then 3 divides d.
2. `all_degree_three`: a triangulated sphere (V - E + F = 2, 2E = 3F) in which every vertex has
   degree 3 (2E = 3V) has V = 4.
3. `one_triple`: d = 3k with angle sum k*pi < 2*pi forces k = 1, so d = 3.
Not checked in Lean: the geometry (faces of a convex polyhedron meet edge to edge, outward
orientation makes the cyclic order of labels the same on every face, a convex vertex has angle sum
below 2*pi, a disphenoid has acute faces).
-/

def lab (L0 : Nat) (i : Nat) : Nat := (L0 + 2 * i) % 3

theorem lab_succ (L0 i : Nat) : lab L0 (i + 1) = (lab L0 i + 2) % 3 := by
  unfold lab; omega

theorem rec_closed (L : Nat → Nat) (h0 : L 0 < 3) (h : ∀ i, L (i + 1) = (L i + 2) % 3) :
    ∀ i, L i = lab (L 0) i := by
  intro i
  induction i with
  | zero => unfold lab; omega
  | succ j ih => rw [h j, ih]; unfold lab; omega

theorem label_cycle_rec (L : Nat → Nat) (h0 : L 0 < 3) (h : ∀ i, L (i + 1) = (L i + 2) % 3)
    (d : Nat) (hd : L d = L 0) : d % 3 = 0 := by
  have e := rec_closed L h0 h d
  unfold lab at e; omega

theorem label_cycle (L0 d : Nat) (h : lab L0 d = lab L0 0) : d % 3 = 0 := by
  unfold lab at h; omega

theorem all_degree_three (V E F : Nat) (h1 : V + F = E + 2) (h2 : 2 * E = 3 * F)
    (h3 : 2 * E = 3 * V) : V = 4 := by
  omega

theorem one_triple (k : Nat) (hk : 0 < k) (h : k < 2) : k = 1 := by
  omega
