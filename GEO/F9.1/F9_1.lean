/-
GEO-F9.1 (Croft–Falconer–Guy, Unsolved Problems in Geometry, F9): f(n) is the
largest number of unit circles each through at least 3 points of an n-point
plane set; f(3..8) = 1, 4, 4, 8, 12, 16 are known and f(9) is asked for.
Here: f(9) ≥ 19 (upper bound n(n-1)/3 = 24 by Harborth–Mengersen).

Witness: 9 points z = a + b·ρ with a, b in Z[ω], ω = e^{2πi/3},
ρ = 5/6 + i·√11/6 (the Moser-spindle rotation). Coordinates lie in the real
field K = Q(√3, √11), stored as rational 4-tuples over the basis
1, √3, √11, √33.

Checked here (core Lean, `decide` / `decide +kernel`):
* `F9_1_main`: the 9 points are pairwise distinct, the 19 centres are pairwise
  distinct, and each centre has squared distance exactly 1 to 3 listed,
  distinct points, all computed in the 4-tuple model of K.
Not checked here: that the 4-tuple multiplication is the arithmetic of
Q(√3, √11) ⊂ ℝ (it encodes √3² = 3, √11² = 11, √3·√11 = √33, which is the
definition of the basis), and the upper side (f(9) ≤ 24 is cited, not proved).
-/

structure K where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
deriving DecidableEq

def K.add (x y : K) : K := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def K.sub (x y : K) : K := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
/-- Product with s3² = 3, s11² = 11, s3·s11 = s33, s3·s33 = 3·s11,
s11·s33 = 11·s3, s33² = 33. -/
def K.mul (x y : K) : K :=
  ⟨x.a*y.a + 3*x.b*y.b + 11*x.c*y.c + 33*x.d*y.d,
   x.a*y.b + x.b*y.a + 11*x.c*y.d + 11*x.d*y.c,
   x.a*y.c + x.c*y.a + 3*x.b*y.d + 3*x.d*y.b,
   x.a*y.d + x.d*y.a + x.b*y.c + x.c*y.b⟩

abbrev Pt := K × K

def d2 (p q : Pt) : K :=
  let dx := K.sub p.1 q.1
  let dy := K.sub p.2 q.2
  K.add (K.mul dx dx) (K.mul dy dy)

def oneK : K := ⟨1, 0, 0, 0⟩

def pts : List Pt := [
  (⟨(-1/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (-1/12 : Rat), (1/12 : Rat), (0 : Rat)⟩),
  (⟨(-1/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (1/12 : Rat), (1/12 : Rat), (0 : Rat)⟩),
  (⟨(5/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (5/12 : Rat), (1/12 : Rat), (0 : Rat)⟩),
  (⟨(5/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (-5/12 : Rat), (1/12 : Rat), (0 : Rat)⟩),
  (⟨(11/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (1/12 : Rat), (1/12 : Rat), (0 : Rat)⟩),
  (⟨(1 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩),
  (⟨(-1 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩),
  (⟨(0 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩),
  (⟨(11/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (-1/12 : Rat), (1/12 : Rat), (0 : Rat)⟩)]

def circs : List (Pt × Nat × Nat × Nat) := [
  ((⟨(1/6 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (0 : Rat), (-1/6 : Rat), (0 : Rat)⟩), 0, 1, 5),
  ((⟨(11/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (-1/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 0, 2, 4),
  ((⟨(-7/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (5/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 0, 2, 6),
  ((⟨(-1/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (1/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 0, 3, 4),
  ((⟨(5/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (-7/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 0, 3, 8),
  ((⟨(-1/2 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (-1/2 : Rat), (0 : Rat), (0 : Rat)⟩), 0, 6, 7),
  ((⟨(5/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (5/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 0, 7, 8),
  ((⟨(5/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (7/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 1, 2, 4),
  ((⟨(-1/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (-1/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 1, 2, 8),
  ((⟨(-7/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (-5/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 1, 3, 6),
  ((⟨(11/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (1/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 1, 3, 8),
  ((⟨(5/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (-5/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 1, 4, 7),
  ((⟨(-1/2 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (1/2 : Rat), (0 : Rat), (0 : Rat)⟩), 1, 6, 7),
  ((⟨(0 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩), 2, 3, 5),
  ((⟨(5/6 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (0 : Rat), (1/6 : Rat), (0 : Rat)⟩), 2, 3, 7),
  ((⟨(17/12 : Rat), (0 : Rat), (0 : Rat), (-1/12 : Rat)⟩, ⟨(0 : Rat), (5/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 2, 5, 8),
  ((⟨(17/12 : Rat), (0 : Rat), (0 : Rat), (1/12 : Rat)⟩, ⟨(0 : Rat), (-5/12 : Rat), (1/12 : Rat), (0 : Rat)⟩), 3, 4, 5),
  ((⟨(1/2 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (1/2 : Rat), (0 : Rat), (0 : Rat)⟩), 4, 5, 7),
  ((⟨(1/2 : Rat), (0 : Rat), (0 : Rat), (0 : Rat)⟩, ⟨(0 : Rat), (-1/2 : Rat), (0 : Rat), (0 : Rat)⟩), 5, 7, 8)]


def circOk (e : Pt × Nat × Nat × Nat) : Bool :=
  match e with
  | (c, i, j, k) =>
    decide (i < j) && decide (j < k) && decide (k < 9) &&
    decide (d2 c (pts.getD i c) = oneK) && decide (d2 c (pts.getD j c) = oneK) &&
    decide (d2 c (pts.getD k c) = oneK)

theorem pts_len : pts.length = 9 := by decide
theorem pts_nodup : pts.Nodup := by decide +kernel
theorem circs_len : circs.length = 19 := by decide
theorem centres_nodup : (circs.map (·.1)).Nodup := by decide +kernel
theorem circs_ok : circs.all circOk = true := by decide +kernel

theorem F9_1_main :
    pts.length = 9 ∧ pts.Nodup ∧ circs.length = 19 ∧ (circs.map (·.1)).Nodup ∧
    circs.all circOk = true :=
  ⟨pts_len, pts_nodup, circs_len, centres_nodup, circs_ok⟩
