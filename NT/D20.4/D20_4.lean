/-
Guy, Unsolved Problems in Number Theory (3rd ed.), D20: a lattice 7-cluster,
i.e. seven points of Z^2, no three on a line, no four on a circle, all
pairwise distances integers. Example: the smallest 7-cluster of
Kurz, Noll, Rathbun, Simmons, Serdica J. Computing 8 (2014) 47-70
(arXiv:1312.2318), diameter 2262000.

Checked here (core Lean, kernel `decide`):
  * the seven points are distinct;
  * every squared distance is the square of the listed integer distance;
  * every three distinct points have nonzero cross product (not collinear);
  * every four distinct points have nonzero determinant
    det [x^2+y^2, x, y, 1] (not concyclic).
  * hence no four distinct points satisfy one equation
    A(x^2+y^2) + Dx + Ey + F = 0 with A != 0 (`D20_4_main`, via the
    Cramer identity A * det = 0 proved by `grind`).
Not checked here: that every circle through three lattice points has such
an equation with integer A, D, E, F (its centre is rational, being the
intersection of two perpendicular bisectors with rational equations).
-/

def P : Fin 7 → Int × Int
  | 0 => (0, 0)
  | 1 => (374400, -2230800)
  | 2 => (1081600, -1488240)
  | 3 => (-453024, -1630200)
  | 4 => (426725, -1630200)
  | 5 => (569088, -1291680)
  | 6 => (-439040, -1308720)

def Drows : List (List Int) :=
  [[0, 2262000, 1839760, 1691976, 1685125, 1411488, 1380400],
   [2262000, 0, 1025440, 1022424, 602875, 959088, 1229600],
   [1839760, 1025440, 0, 1541176, 670085, 548912, 1531200],
   [1691976, 1022424, 1541176, 0, 879749, 1076712, 321784],
   [1685125, 602875, 670085, 879749, 0, 367237, 923525],
   [1411488, 959088, 548912, 1076712, 367237, 0, 1008272],
   [1380400, 1229600, 1531200, 321784, 923525, 1008272, 0]]

/-- the integer distance between points i and j. -/
def Dm (i j : Fin 7) : Int := (Drows.getD i.val []).getD j.val 0

def dist2 (p q : Int × Int) : Int := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def cross (a b c : Int × Int) : Int :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def det3 (a b c d e f g h i : Int) : Int :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- det of the rows [x^2+y^2, x, y, 1] for four points. -/
def circDet (p q r s : Int × Int) : Int :=
  let w := fun (t : Int × Int) => t.1 ^ 2 + t.2 ^ 2
  w p * det3 q.1 q.2 1 r.1 r.2 1 s.1 s.2 1
  - p.1 * det3 (w q) q.2 1 (w r) r.2 1 (w s) s.2 1
  + p.2 * det3 (w q) q.1 1 (w r) r.1 1 (w s) s.1 1
  - det3 (w q) q.1 q.2 (w r) r.1 r.2 (w s) s.1 s.2

theorem D20_4_distinct : ∀ i j : Fin 7, i ≠ j → P i ≠ P j := by decide +kernel

theorem D20_4_dist : ∀ i j : Fin 7, 0 ≤ Dm i j ∧ Dm i j ^ 2 = dist2 (P i) (P j) := by
  decide +kernel

theorem D20_4_noncollinear :
    ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → cross (P i) (P j) (P k) ≠ 0 := by
  decide +kernel

theorem D20_4_nonconcyclic :
    ∀ i j k l : Fin 7, i < j → j < k → k < l → circDet (P i) (P j) (P k) (P l) ≠ 0 := by
  decide +kernel

def det4 (w1 x1 y1 w2 x2 y2 w3 x3 y3 w4 x4 y4 : Int) : Int :=
  w1 * det3 x2 y2 1 x3 y3 1 x4 y4 1
  - x1 * det3 w2 y2 1 w3 y3 1 w4 y4 1
  + y1 * det3 w2 x2 1 w3 x3 1 w4 x4 1
  - det3 w2 x2 y2 w3 x3 y3 w4 x4 y4

theorem cramerA (w1 x1 y1 w2 x2 y2 w3 x3 y3 w4 x4 y4 A D E F : Int)
    (h1 : A * w1 + D * x1 + E * y1 + F = 0) (h2 : A * w2 + D * x2 + E * y2 + F = 0)
    (h3 : A * w3 + D * x3 + E * y3 + F = 0) (h4 : A * w4 + D * x4 + E * y4 + F = 0) :
    A * det4 w1 x1 y1 w2 x2 y2 w3 x3 y3 w4 x4 y4 = 0 := by
  unfold det4 det3
  grind

/-- the point p lies on the curve A(x^2+y^2) + Dx + Ey + F = 0. -/
def OnCirc (A D E F : Int) (p : Int × Int) : Prop :=
  A * (p.1 ^ 2 + p.2 ^ 2) + D * p.1 + E * p.2 + F = 0

theorem circDet_eq (p q r s : Int × Int) :
    circDet p q r s = det4 (p.1 ^ 2 + p.2 ^ 2) p.1 p.2 (q.1 ^ 2 + q.2 ^ 2) q.1 q.2
      (r.1 ^ 2 + r.2 ^ 2) r.1 r.2 (s.1 ^ 2 + s.2 ^ 2) s.1 s.2 := rfl

theorem D20_4_nocircle (i j k l : Fin 7) (hij : i < j) (hjk : j < k) (hkl : k < l)
    (A D E F : Int) (hA : A ≠ 0) (hi : OnCirc A D E F (P i)) (hj : OnCirc A D E F (P j))
    (hk : OnCirc A D E F (P k)) (hl : OnCirc A D E F (P l)) : False := by
  have h := cramerA _ _ _ _ _ _ _ _ _ _ _ _ A D E F hi hj hk hl
  rw [← circDet_eq] at h
  have hd := D20_4_nonconcyclic i j k l hij hjk hkl
  rcases Int.mul_eq_zero.mp h with h0 | h0
  · exact hA h0
  · exact hd h0

/-- Main: seven distinct points of Z^2 with integral mutual distances,
no three collinear, no four on a common circle A(x^2+y^2)+Dx+Ey+F = 0. -/
theorem D20_4_main :
    (∀ i j : Fin 7, i ≠ j → P i ≠ P j) ∧
    (∀ i j : Fin 7, ∃ d : Int, 0 ≤ d ∧ d ^ 2 = dist2 (P i) (P j)) ∧
    (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → cross (P i) (P j) (P k) ≠ 0) ∧
    (∀ i j k l : Fin 7, i < j → j < k → k < l → ∀ A D E F : Int, A ≠ 0 →
      ¬ (OnCirc A D E F (P i) ∧ OnCirc A D E F (P j) ∧ OnCirc A D E F (P k) ∧
         OnCirc A D E F (P l))) :=
  ⟨D20_4_distinct, fun i j => ⟨Dm i j, D20_4_dist i j⟩, D20_4_noncollinear,
   fun i j k l hij hjk hkl A D E F hA ⟨hi, hj, hk, hl⟩ =>
     D20_4_nocircle i j k l hij hjk hkl A D E F hA hi hj hk hl⟩
