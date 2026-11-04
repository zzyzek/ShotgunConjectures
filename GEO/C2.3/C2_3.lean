/-
GEO-C2.3 (Croft–Falconer–Guy, C2, Moroń): "is there a rectangle which can be
squared in two distinct ways with no square occurring in both squarings?"
Yes: 593 × 422.

Checked here (core Lean, no Mathlib; all by `decide`; from
../open-problems/lean/Rectangles.lean): `c23a` and `c23b` are each 13
squares inside 593 × 422 with pairwise disjoint interiors and total area
593 · 422, each with distinct sides, and no side occurs in both.
Not checked here: the standard fact that "inside + pairwise disjoint
interiors + total area W·H" implies an exact cover (squares with integer
corners; an uncovered unit cell would leave area missing). The cover was
also checked cell by cell in Python (certificate/).
-/

structure Sq where
  s : Nat
  x : Nat
  y : Nat

def inside (W H : Nat) (q : Sq) : Bool := q.x + q.s ≤ W && q.y + q.s ≤ H

def apart (p q : Sq) : Bool :=
  p.x + p.s ≤ q.x || q.x + q.s ≤ p.x || p.y + p.s ≤ q.y || q.y + q.s ≤ p.y

def pairwiseApart : List Sq → Bool
  | [] => true
  | q :: qs => qs.all (apart q) && pairwiseApart qs

def area (l : List Sq) : Nat := (l.map (fun q => q.s * q.s)).foldl (· + ·) 0

def isTiling (W H : Nat) (l : List Sq) : Bool :=
  l.all (inside W H) && pairwiseApart l && area l == W * H

def sides (l : List Sq) : List Nat := l.map Sq.s

def distinct : List Nat → Bool
  | [] => true
  | a :: as => !(as.contains a) && distinct as

def c23a : List Sq :=
  [⟨2, 341, 205⟩, ⟨22, 200, 222⟩, ⟨37, 341, 207⟩, ⟨39, 302, 205⟩, ⟨41, 302, 164⟩,
   ⟨43, 343, 164⟩, ⟨80, 222, 164⟩, ⟨164, 222, 0⟩, ⟨178, 200, 244⟩, ⟨200, 0, 222⟩,
   ⟨207, 386, 0⟩, ⟨215, 378, 207⟩, ⟨222, 0, 0⟩]

def c23b : List Sq :=
  [⟨18, 278, 85⟩, ⟨38, 363, 230⟩, ⟨49, 247, 103⟩, ⟨67, 296, 85⟩, ⟨72, 175, 103⟩,
   ⟨85, 278, 0⟩, ⟨103, 175, 0⟩, ⟨116, 247, 152⟩, ⟨154, 247, 268⟩, ⟨175, 0, 0⟩,
   ⟨192, 401, 230⟩, ⟨230, 363, 0⟩, ⟨247, 0, 175⟩]

theorem geo_c2_3_tiling_a : isTiling 593 422 c23a = true := by decide
theorem geo_c2_3_tiling_b : isTiling 593 422 c23b = true := by decide
theorem geo_c2_3_perfect_a : distinct (sides c23a) = true := by decide
theorem geo_c2_3_perfect_b : distinct (sides c23b) = true := by decide
theorem geo_c2_3_disjoint_sizes : (sides c23a).all (fun s => !(sides c23b).contains s) = true := by decide
