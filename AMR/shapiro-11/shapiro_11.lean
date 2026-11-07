/-
AMR shapiro-11, shapiro-12, shapiro-13: Forsgard-Shapiro Conjectures 8, 9, 10
(B. Shapiro, "Problems around polynomials: the good, the bad and the ugly",
Arnold Math. J. 1 (2015), arXiv 1503.05295, Section 7).

For f = sum a_k x^k of degree n with all a_k > 0:
* Conj 8: #real zeros <= number of corners of t |-> max_k (log a_k + k t + log C(n,k)).
* Conj 9: #real zeros <= v~(f), the number of parity changes along the increasing list of
  indices k with c~_k = (k+1) a_k^2 - k a_(k-1) a_(k+1) > 0 (a_(-1) = a_(n+1) = 0).
* Conj 10: the same with c_k = a_k^2 - a_(k-1) a_(k+1) >= 0.

Counterexample to all three.  P = (19x^2 - 94x + 163) * prod_{j<22} (2D x + 2D + 2j - 23),
D = 10^5, degree 24, all coefficients positive.  It has the 22 distinct rational zeros
x_j = -(2D + 2j - 23)/(2D), while corners = 21, v = 20, v~ = 20.

Checked here (core Lean, `decide`):
* `P` is the coefficient list (index k = coefficient of x^k) of that product, of length 25,
  every entry positive;
* `homEval P (rootNum j) (2D) = 0` for each j < 22, where
  homEval a p q = sum_k a_k p^k q^(24-k) = q^24 * P(p/q); the 22 numerators are distinct;
* `corners P = 21`: the strict vertices of the upper hull of the points
  (k, log(a_k C(24,k))) are counted by the exact test
  w_i^(l-j) w_l^(j-i) < w_j^(l-i) for all i < j < l (w_k = a_k C(24,k)), and corners = vertices - 1;
* `vPar P false = 20` (Conj 10) and `vPar P true = 20` (Conj 9).

Not checked in Lean (definitional reading only): that homEval = 0 means P(p/q) = 0; that
the corners of a maximum of affine functions are the edges of the upper hull of
(k, log w_k) between consecutive strict vertices.
-/


def polyAdd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: polyAdd p q

def polyMul : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => polyAdd (q.map (fun b => a * b)) (0 :: polyMul p q)

def D : Int := 100000

def lin (j : Nat) : List Int := [2 * D + 2 * (j : Int) - 23, 2 * D]

/-- Coefficients of P, lowest degree first. -/
def P : List Int :=
  (List.range 22).foldl (fun acc j => polyMul acc (lin j)) [163, -94, 19]

def rootNum (j : Nat) : Int := -(2 * D + 2 * (j : Int) - 23)

/-- `homEval a p q = sum_k a_k p^k q^(deg-k)`, i.e. `q^deg * a(p/q)`. -/
def homEval (a : List Int) (p q : Int) : Int :=
  let n := a.length - 1
  ((List.range a.length).map (fun k => a.getD k 0 * p ^ k * q ^ (n - k))).foldl (· + ·) 0

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def binom (n k : Nat) : Nat := fact n / (fact k * fact (n - k))

def wt (a : List Int) (k : Nat) : Nat := (a.getD k 0).toNat * binom (a.length - 1) k

def strictVertex (a : List Int) (j : Nat) : Bool :=
  let n := a.length - 1
  (List.range j).all fun i =>
    ((List.range (n + 1)).filter (fun l => j < l)).all fun l =>
      decide (wt a i ^ (l - j) * wt a l ^ (j - i) < wt a j ^ (l - i))

def corners (a : List Int) : Nat :=
  ((List.range a.length).filter (strictVertex a)).length - 1

def coef (a : List Int) (k : Int) : Int :=
  if k < 0 then 0 else a.getD k.toNat 0

def keep (a : List Int) (tilde : Bool) (k : Nat) : Bool :=
  let ak := coef a k
  let am := coef a ((k : Int) - 1)
  let ap := coef a ((k : Int) + 1)
  if tilde then decide (0 < ((k : Int) + 1) * ak * ak - (k : Int) * am * ap)
  else decide (0 ≤ ak * ak - am * ap)

def parityChanges : List Nat → Nat
  | x :: y :: r => (if x % 2 = y % 2 then 0 else 1) + parityChanges (y :: r)
  | _ => 0

def vPar (a : List Int) (tilde : Bool) : Nat :=
  parityChanges ((List.range a.length).filter (keep a tilde))

theorem P_length : P.length = 25 := by decide +kernel

theorem P_pos : P.all (fun c => decide (0 < c)) = true := by decide +kernel

theorem P_roots :
    (List.range 22).all (fun j => decide (homEval P (rootNum j) (2 * D) = 0)) = true := by
  decide +kernel

theorem roots_distinct (i j : Nat) (h : rootNum i = rootNum j) : i = j := by
  unfold rootNum at h
  omega

theorem P_corners : corners P = 21 := by decide +kernel

theorem P_v : vPar P false = 20 := by decide +kernel

theorem P_vtilde : vPar P true = 20 := by decide +kernel

/-- Main theorem: a degree-24 polynomial with positive coefficients and 22 distinct rational
zeros whose tropical corner count (Conj 8) is 21 and whose parity counts v~ (Conj 9) and
v (Conj 10) are 20. -/
theorem shapiro_conj_8_9_10_counterexample :
    P.length = 25 ∧ P.all (fun c => decide (0 < c)) = true ∧
    (List.range 22).all (fun j => decide (homEval P (rootNum j) (2 * D) = 0)) = true ∧
    (∀ i j, rootNum i = rootNum j → i = j) ∧
    corners P = 21 ∧ vPar P true = 20 ∧ vPar P false = 20 :=
  ⟨P_length, P_pos, P_roots, roots_distinct, P_corners, P_vtilde, P_v⟩

