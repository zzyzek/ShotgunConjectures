/-
CFG A12 (Fickett, congruent triangles): an explicit counterexample to
  sin(psi/2) <= length(dK ∩ K') / length(dK' ∩ K) <= 1/sin(psi/2),
psi the least angle.

K  = triangle (-5,0), (5,0), (0,12): sides 10, 13, 13; least angle psi at (0,12) with
     sin(psi/2) = 5/13 (half the base over a leg).
K' = rotation of K by (cos, sin) = (-5/13, -12/13), then translation by (-31/10, 46/10).

Checked here (core Lean, exact rationals, `decide +kernel`):
* K' is that rigid image of K (cos^2 + sin^2 = 1) and both are counter-clockwise;
* squared side lengths are 100, 169, 169 for both triangles, and sin(psi/2) = 5/13 is the
  half-base / leg ratio of the apex angle (the apex angle is the least: 10 < 13);
* `frac A i B` = the fraction of side i of A lying in B (Liang-Barsky clipping of the
  segment against the three half-planes of B); L1 = sum of frac K i K' * |side i|,
  L2 = sum of frac K' i K * |side i|;
* L1 = 687563/26910, L2 = 2363/414, and L1 / L2 > 13/5 = 1/sin(psi/2).
Not checked here: that the clipping formula equals the length of the side inside the other
triangle (standard: a convex set meets a segment in a sub-segment, given by intersecting
the parameter intervals of the half-planes), and that the boundary parts on the other
triangle's boundary have length zero (no two sides here are collinear).
-/

structure P where
  x : Rat
  y : Rat
deriving DecidableEq

def K : List P := [⟨-5, 0⟩, ⟨5, 0⟩, ⟨0, 12⟩]

def cs : Rat := -5/13
def sn : Rat := -12/13
def dx : Rat := -31/10
def dy : Rat := 46/10

def move (p : P) : P := ⟨cs * p.x - sn * p.y + dx, sn * p.x + cs * p.y + dy⟩

def K' : List P := K.map move

def vtx (T : List P) (i : Nat) : P := T.getD (i % 3) ⟨0, 0⟩

def orient (T : List P) : Rat :=
  let a := vtx T 0; let b := vtx T 1; let c := vtx T 2
  (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

def sq (T : List P) (i : Nat) : Rat :=
  let a := vtx T i; let b := vtx T (i+1)
  (b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y)

/-- One clipping step: restrict [t0,t1] to the parameters where the point is left of edge j of B. -/
def step (p q : P) (B : List P) (j : Nat) (iv : Rat × Rat) : Rat × Rat :=
  let a := vtx B j; let b := vtx B (j+1)
  let ex := b.x - a.x; let ey := b.y - a.y
  let f0 := ex * (p.y - a.y) - ey * (p.x - a.x)
  let f1 := ex * (q.y - a.y) - ey * (q.x - a.x)
  let d := f1 - f0
  if d = 0 then (if f0 ≤ 0 then (1, 0) else iv)
  else if 0 < d then (max iv.1 (-f0 / d), iv.2)
  else (iv.1, min iv.2 (-f0 / d))

def frac (A : List P) (i : Nat) (B : List P) : Rat :=
  let p := vtx A i; let q := vtx A (i+1)
  let iv := step p q B 2 (step p q B 1 (step p q B 0 (0, 1)))
  max 0 (iv.2 - iv.1)

/-- side lengths of K (and K'): side i joins vertex i to vertex i+1. -/
def len : Nat → Rat
  | 0 => 10
  | _ => 13

def Lsum (A B : List P) : Rat := frac A 0 B * len 0 + frac A 1 B * len 1 + frac A 2 B * len 2

theorem rotation_ok : cs * cs + sn * sn = 1 := by decide +kernel

theorem orient_pos : 0 < orient K ∧ 0 < orient K' := by decide +kernel

theorem sides_K : sq K 0 = 100 ∧ sq K 1 = 169 ∧ sq K 2 = 169 := by decide +kernel

theorem sides_K' : sq K' 0 = 100 ∧ sq K' 1 = 169 ∧ sq K' 2 = 169 := by decide +kernel

theorem L1_val : Lsum K K' = 687563 / 26910 := by decide +kernel

theorem L2_val : Lsum K' K = 2363 / 414 := by decide +kernel

/-- Main: the ratio L1/L2 exceeds 1/sin(psi/2) = 13/5. -/
theorem fickett_triangle_counterexample : 13 / 5 < Lsum K K' / Lsum K' K := by
  rw [L1_val, L2_val]; decide +kernel
