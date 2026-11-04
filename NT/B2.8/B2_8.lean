/-
NT-B2.8 (Guy, UPINT 3rd ed., B2, Goto–Shibata): "if a harmonic number n has
H(n) = 3p with p prime, is n arithmetic (d(n) ∣ σ(n))?"  No.

Witness: n = 2^8·7·19^2·37·73·113·127 = 25075635936512 with H(n) = 339 = 3·113,
σ(n) mod d(n) = 288.  Second witness: 12757657068800 = 2^8·5^2·7·19·31·37·73·179,
H = 537 = 3·179, σ mod d = 576.

Checked here (core Lean, no Mathlib; `decide`), σ and d by the product
formulas over the given prime-power lists:
* `w1`, `w2`: the values, primality of the bases, H(n) = 3p with p prime,
  and σ(n) mod d(n) ≠ 0.
Not checked here: that σ and d are given by the product formulas
(multiplicativity), as in NT/B2_7.lean.
-/

def isPrimeSmall (p : Nat) : Bool := 2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0)

abbrev PF := List (Nat × Nat)

def val (f : PF) : Nat := f.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
def sig (f : PF) : Nat := f.foldl (fun acc pe => acc * ((pe.1 ^ (pe.2 + 1) - 1) / (pe.1 - 1))) 1
def nd (f : PF) : Nat := f.foldl (fun acc pe => acc * (pe.2 + 1)) 1

def check (f : PF) (n p : Nat) : Bool :=
  val f == n && f.all (fun pe => isPrimeSmall pe.1) && isPrimeSmall p &&
  (val f * nd f) % sig f == 0 && val f * nd f / sig f == 3 * p && sig f % nd f != 0

theorem w1 : check [(2, 8), (7, 1), (19, 2), (37, 1), (73, 1), (113, 1), (127, 1)] 25075635936512 113 = true ∧
    sig [(2, 8), (7, 1), (19, 2), (37, 1), (73, 1), (113, 1), (127, 1)] %
      nd [(2, 8), (7, 1), (19, 2), (37, 1), (73, 1), (113, 1), (127, 1)] = 288 := by decide
theorem w2 : check [(2, 8), (5, 2), (7, 1), (19, 1), (31, 1), (37, 1), (73, 1), (179, 1)] 12757657068800 179 = true := by
  decide
