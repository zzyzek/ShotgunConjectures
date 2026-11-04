/-
GEO-C2.1 (Croft–Falconer–Guy, C2, Moroń): "in a squared rectangle, are there
always at least two squares which are surrounded by (four) larger ones?"
No, under every reading: the classical order-9 perfect rectangle 61 × 69.

A square is counted as "surrounded" (most permissive reading) if it does not
touch the boundary of the rectangle and every square sharing a boundary
segment of positive length with it is larger.  Stricter readings can only
lower the count.

Checked here (core Lean, no Mathlib; all by `decide`):
* `geo_c2_1_tiling`, `geo_c2_1_perfect`: the 9 squares lie inside 61 × 69
  (x-extent 61, y-extent 69), have pairwise disjoint interiors, total area
  61 · 69 and distinct sides;
* `geo_c2_1_count`: exactly one square (side 2) is surrounded.
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

def touchesBoundary (W H : Nat) (q : Sq) : Bool :=
  q.x == 0 || q.y == 0 || q.x + q.s == W || q.y + q.s == H

/-- p and q share a boundary segment of positive length. -/
def adjacent (p q : Sq) : Bool :=
  ((p.x + p.s == q.x || q.x + q.s == p.x) && (max p.y q.y < min (p.y + p.s) (q.y + q.s))) ||
  ((p.y + p.s == q.y || q.y + q.s == p.y) && (max p.x q.x < min (p.x + p.s) (q.x + q.s)))

def surrounded (W H : Nat) (l : List Sq) (q : Sq) : Bool :=
  !touchesBoundary W H q && l.all (fun p => !adjacent p q || q.s < p.s)

def c21 : List Sq :=
  [⟨2, 36, 34⟩, ⟨5, 33, 36⟩, ⟨7, 38, 34⟩, ⟨9, 36, 25⟩, ⟨16, 45, 25⟩,
   ⟨25, 36, 0⟩, ⟨28, 33, 41⟩, ⟨33, 0, 36⟩, ⟨36, 0, 0⟩]

theorem geo_c2_1_tiling : isTiling 61 69 c21 = true := by decide
theorem geo_c2_1_perfect : distinct (sides c21) = true := by decide
theorem geo_c2_1_count : (c21.filter (surrounded 61 69 c21)).map Sq.s = [2] := by decide
