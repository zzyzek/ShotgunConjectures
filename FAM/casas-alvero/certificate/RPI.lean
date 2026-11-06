import Mathlib

/-!
# Reflective polynomial identity checker (RPI)

Sparse multivariate polynomials over `ℤ` are lists of `(exponent list, Int)` pairs.
`RPI.check fs gs t` computes `Σ fs_i * gs_i` with a normalising (sorted merge) add and
multiply and compares the result with `t` syntactically. `RPI.check_eval` says that if
`check fs gs t = true` then `Σ fs_i(x) * gs_i(x) = t(x)` for every point `x` in every
commutative ring. The soundness proofs do not use the ordering: an unsorted input can only
make `check` return `false`. The intended use is `decide +kernel`: the kernel evaluates
`check` with GMP-backed `Nat` arithmetic, so no `ring` normalisation happens in the elaborator.
-/

namespace RPI

/-- An exponent vector. -/
abbrev Mono := List Nat
/-- A sparse polynomial: terms `(exponents, coefficient)`, intended sorted by `Mono.blt`. -/
abbrev Poly := List (Mono × Int)

def Mono.mul : Mono → Mono → Mono
  | [], m => m
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: Mono.mul as bs

def Mono.beq : Mono → Mono → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && Mono.beq as bs
  | _, _ => false

/-- Lexicographic order; used only to keep sums sorted, never in a soundness proof. -/
def Mono.blt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => Nat.blt a b || (Nat.beq a b && Mono.blt as bs)

def izero : Int → Bool
  | .ofNat n => Nat.beq n 0
  | .negSucc _ => false

def ieq : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.beq a b
  | .negSucc a, .negSucc b => Nat.beq a b
  | _, _ => false

/-- Insert-merge of the term `t` (followed by `p`) into `q`; `r` is `add p`. -/
def addAux (t : Mono × Int) (p : Poly) (r : Poly → Poly) : Poly → Poly
  | [] => t :: p
  | s :: q =>
    cond (Mono.beq t.1 s.1)
      (cond (izero (t.2 + s.2)) (r q) ((t.1, t.2 + s.2) :: r q))
      (cond (Mono.blt t.1 s.1) (t :: r (s :: q)) (s :: addAux t p r q))

/-- Merge-add of two sorted polynomials. -/
def add : Poly → Poly → Poly
  | [], q => q
  | t :: p, q => addAux t p (add p) q

def mulTerm (t : Mono × Int) : Poly → Poly
  | [] => []
  | s :: q => (Mono.mul t.1 s.1, t.2 * s.2) :: mulTerm t q

/-- Product; cost is `|p|` merges, so put the short factor first. -/
def mul : Poly → Poly → Poly
  | [], _ => []
  | t :: p, q => add (mulTerm t q) (mul p q)

def sumProd : List Poly → List Poly → Poly
  | f :: fs, g :: gs => add (mul f g) (sumProd fs gs)
  | _, _ => []

def Poly.beq : Poly → Poly → Bool
  | [], [] => true
  | (m, c) :: p, (m', c') :: q => Mono.beq m m' && ieq c c' && Poly.beq p q
  | _, _ => false

/-- Every monomial of `p` has at most `n` exponents. -/
def Poly.lenLe (n : Nat) : Poly → Bool
  | [] => true
  | (m, _) :: p => Nat.ble m.length n && Poly.lenLe n p

/-- The checker: `Σ fs_i * gs_i` normalises to `t`. -/
def check (fs gs : List Poly) (t : Poly) : Bool := Poly.beq (sumProd fs gs) t

open Lean Meta in
/-- `rpi% "e,e,..:c;e,e,..:c"` elaborates directly to the `RPI.Poly` literal with raw `Nat`
literals (no numeral elaboration). Only the resulting term is trusted; the kernel checks it. -/
elab "rpi% " s:str : term => show Elab.TermElabM Expr from do
  let natT := mkConst ``Nat
  let monoT ← mkAppM ``List #[natT]
  let termT ← mkAppM ``Prod #[monoT, mkConst ``Int]
  let mut ts : Array Expr := #[]
  for tm in s.getString.splitOn ";" do
    if tm.isEmpty then continue
    match tm.splitOn ":" with
    | [es, c] =>
      let mut ex : Array Expr := #[]
      for e in es.splitOn "," do
        match e.toNat? with
        | some n => ex := ex.push (mkRawNatLit n)
        | none => throwError "rpi%: bad exponent {e}"
      let m ← mkListLit natT ex.toList
      let ce ← match c.toInt? with
        | some (.ofNat n) => pure (mkApp (mkConst ``Int.ofNat) (mkRawNatLit n))
        | some (.negSucc n) => pure (mkApp (mkConst ``Int.negSucc) (mkRawNatLit n))
        | none => throwError "rpi%: bad coefficient {c}"
      ts := ts.push (mkApp4 (mkConst ``Prod.mk [0, 0]) monoT (mkConst ``Int) m ce)
    | _ => throwError "rpi%: bad term {tm}"
  mkListLit termT ts.toList

section eval

variable {R : Type*} [CommRing R]

/-- Evaluation of a monomial at the point `xs` (missing coordinates read as `0`). -/
def Mono.eval : List R → Mono → R
  | _, [] => 1
  | [], e :: es => 0 ^ e * Mono.eval [] es
  | x :: xs, e :: es => x ^ e * Mono.eval xs es

def Poly.eval (xs : List R) : Poly → R
  | [] => 0
  | (m, c) :: p => (c : R) * Mono.eval xs m + Poly.eval xs p

def sumProdEval (xs : List R) : List Poly → List Poly → R
  | f :: fs, g :: gs => Poly.eval xs f * Poly.eval xs g + sumProdEval xs fs gs
  | _, _ => 0

theorem Mono.eval_mul (xs : List R) (a b : Mono) :
    Mono.eval xs (Mono.mul a b) = Mono.eval xs a * Mono.eval xs b := by
  induction a generalizing b xs with
  | nil => simp [Mono.mul, Mono.eval]
  | cons e es ih =>
    cases b with
    | nil => simp [Mono.mul, Mono.eval]
    | cons f fs =>
      cases xs with
      | nil =>
        simp only [Mono.mul, Mono.eval, ih, pow_add]
        ring
      | cons x xs =>
        simp only [Mono.mul, Mono.eval, ih, pow_add]
        ring

theorem Mono.eq_of_beq : ∀ {a b : Mono}, Mono.beq a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Mono.beq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, Mono.eq_of_beq h.2]
  | [], _ :: _, h => by simp [Mono.beq] at h
  | _ :: _, [], h => by simp [Mono.beq] at h

theorem izero_eq {c : Int} (h : izero c = true) : c = 0 := by
  cases c with
  | ofNat n => simp only [izero, Nat.beq_eq] at h; simp [h]
  | negSucc n => simp [izero] at h

theorem ieq_eq : ∀ {a b : Int}, ieq a b = true → a = b
  | .ofNat a, .ofNat b, h => by simp only [ieq, Nat.beq_eq] at h; rw [h]
  | .negSucc a, .negSucc b, h => by simp only [ieq, Nat.beq_eq] at h; rw [h]
  | .ofNat _, .negSucc _, h => by simp [ieq] at h
  | .negSucc _, .ofNat _, h => by simp [ieq] at h

theorem Poly.eq_of_beq : ∀ {p q : Poly}, Poly.beq p q = true → p = q
  | [], [], _ => rfl
  | (m, c) :: p, (m', c') :: q, h => by
    simp only [Poly.beq, Bool.and_eq_true] at h
    rw [Mono.eq_of_beq h.1.1, ieq_eq h.1.2, Poly.eq_of_beq h.2]
  | [], _ :: _, h => by simp [Poly.beq] at h
  | _ :: _, [], h => by simp [Poly.beq] at h

theorem addAux_eval (xs : List R) (t : Mono × Int) (p : Poly) (r : Poly → Poly)
    (hr : ∀ q, Poly.eval xs (r q) = Poly.eval xs p + Poly.eval xs q) :
    ∀ q, Poly.eval xs (addAux t p r q) = Poly.eval xs (t :: p) + Poly.eval xs q := by
  obtain ⟨m, c⟩ := t
  intro q
  induction q with
  | nil => simp [addAux, Poly.eval]
  | cons s q ih =>
    obtain ⟨m', c'⟩ := s
    simp only [addAux]
    cases h1 : Mono.beq m m'
    · cases h2 : Mono.blt m m'
      · simp only [Bool.cond_false, Poly.eval, ih]
        ring
      · simp only [Bool.cond_false, Bool.cond_true, Poly.eval, hr]
        ring
    · have e1 := Mono.eq_of_beq h1
      subst e1
      cases h2 : izero (c + c')
      · simp only [Bool.cond_true, Bool.cond_false, Poly.eval, hr, Int.cast_add]
        ring
      · have e2 := izero_eq h2
        simp only [Bool.cond_true, Poly.eval, hr]
        have : (c' : R) = -c := by
          rw [show c' = -c by omega]; push_cast; ring
        rw [this]
        ring

theorem add_eval (xs : List R) (p q : Poly) :
    Poly.eval xs (add p q) = Poly.eval xs p + Poly.eval xs q := by
  induction p generalizing q with
  | nil => simp [add, Poly.eval]
  | cons t p ih => exact addAux_eval xs t p (add p) ih q

theorem mulTerm_eval (xs : List R) (t : Mono × Int) (q : Poly) :
    Poly.eval xs (mulTerm t q) = Poly.eval xs [t] * Poly.eval xs q := by
  obtain ⟨m, c⟩ := t
  induction q with
  | nil => simp [mulTerm, Poly.eval]
  | cons s q ih =>
    obtain ⟨m', c'⟩ := s
    simp only [mulTerm, Poly.eval, ih, Mono.eval_mul, Int.cast_mul]
    ring

theorem mul_eval (xs : List R) (p q : Poly) :
    Poly.eval xs (mul p q) = Poly.eval xs p * Poly.eval xs q := by
  induction p with
  | nil => simp [mul, Poly.eval]
  | cons t p ih =>
    simp only [mul, add_eval, mulTerm_eval, ih]
    obtain ⟨m, c⟩ := t
    simp only [Poly.eval]
    ring

theorem sumProd_eval (xs : List R) : ∀ fs gs : List Poly,
    Poly.eval xs (sumProd fs gs) = sumProdEval xs fs gs
  | f :: fs, g :: gs => by
    simp only [sumProd, sumProdEval, add_eval, mul_eval, sumProd_eval xs fs gs]
  | [], _ => by simp [sumProd, sumProdEval, Poly.eval]
  | _ :: _, [] => by simp [sumProd, sumProdEval, Poly.eval]

/-- Soundness: a successful check is a polynomial identity at every point of every
commutative ring. -/
theorem check_eval (xs : List R) {fs gs : List Poly} {t : Poly} (h : check fs gs t = true) :
    sumProdEval xs fs gs = Poly.eval xs t := by
  rw [← sumProd_eval, Poly.eq_of_beq h]

theorem sumProdEval_eq_zero (xs : List R) : ∀ {fs : List Poly} (gs : List Poly),
    (∀ f ∈ fs, Poly.eval xs f = 0) → sumProdEval xs fs gs = 0
  | f :: fs, g :: gs, h => by
    simp only [sumProdEval, h f (by simp), zero_mul, zero_add]
    exact sumProdEval_eq_zero xs gs fun f' hf' => h f' (by simp [hf'])
  | [], _, _ => by simp [sumProdEval]
  | _ :: _, [], _ => by simp [sumProdEval]

/-- Ideal membership: if every `f_i` vanishes at `xs` and the check succeeds, `t` vanishes. -/
theorem check_zero (xs : List R) {fs gs : List Poly} {t : Poly} (h : check fs gs t = true)
    (hz : ∀ f ∈ fs, Poly.eval xs f = 0) : Poly.eval xs t = 0 := by
  rw [← check_eval xs h, sumProdEval_eq_zero xs gs hz]

theorem Mono.eval_append (xs ys : List R) :
    ∀ m : Mono, m.length ≤ xs.length → Mono.eval (xs ++ ys) m = Mono.eval xs m
  | [], _ => rfl
  | e :: es, h => by
    cases xs with
    | nil => simp at h
    | cons a xs =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at h
      simp only [Mono.eval, List.cons_append, Mono.eval_append xs ys es h]

theorem Poly.eval_append (xs ys : List R) {n : Nat} (hn : xs.length = n) :
    ∀ p : Poly, Poly.lenLe n p = true → Poly.eval (xs ++ ys) p = Poly.eval xs p
  | [], _ => rfl
  | (m, c) :: p, h => by
    simp only [Poly.lenLe, Bool.and_eq_true, Nat.ble_eq] at h
    simp only [Poly.eval, Mono.eval_append xs ys m (hn ▸ h.1), Poly.eval_append xs ys hn p h.2]

end eval
