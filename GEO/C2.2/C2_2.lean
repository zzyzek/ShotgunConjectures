/-
GEO-C2.2 (Croft–Falconer–Guy, Unsolved Problems in Geometry, C2, Moroń):
"in a squared rectangle with relatively prime sides, is there always a square
whose side is a perfect square?"  No.

Checked here (core Lean, no Mathlib; all by `decide`; from
../open-problems/lean/Rectangles.lean): the 14 squares of `c22` lie inside
799 × 689, have pairwise disjoint interiors and total area 799 · 689; their
sides are distinct (perfect); gcd(799, 689) = 1; no side is a perfect square.
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

-- `n` is a perfect square with root below 21; enough when `n < 21 * 21`.
def isSquareSmall (n : Nat) : Bool := (List.range 21).any (fun r => r * r == n)

def c22 : List Sq :=
  [⟨402, 0, 0⟩, ⟨397, 402, 0⟩, ⟨5, 402, 397⟩, ⟨28, 407, 397⟩, ⟨72, 435, 397⟩,
   ⟨292, 507, 397⟩, ⟨287, 0, 402⟩, ⟨67, 287, 402⟩, ⟨30, 354, 402⟩, ⟨23, 384, 402⟩,
   ⟨7, 384, 425⟩, ⟨44, 391, 425⟩, ⟨37, 354, 432⟩, ⟨220, 287, 469⟩]

theorem geo_c2_2_tiling : isTiling 799 689 c22 = true := by decide
theorem geo_c2_2_perfect : distinct (sides c22) = true := by decide
theorem geo_c2_2_coprime : Nat.gcd 799 689 = 1 := by decide
theorem geo_c2_2_sides_small : (sides c22).all (fun s => s < 21 * 21) = true := by decide
theorem geo_c2_2_no_square_side : (sides c22).all (fun s => !isSquareSmall s) = true := by decide
