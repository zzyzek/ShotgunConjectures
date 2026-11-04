/-
NT-B2.7 (Guy, UPINT 3rd ed., B2, Goto–Shibata): "does every harmonic number
have a unique harmonic seed?"  No.

Definitions (Cohen–Sorli): n is harmonic when H(n) = n·d(n)/σ(n) is an
integer; a harmonic seed is a harmonic number > 1 with no smaller harmonic
unitary divisor > 1.  A unitary divisor of n = Π p^e is a product of a
subset of the prime powers p^e.

Witness: n = 2^4·3·5^2·7^2·19·31^2·83·331 = 29495815011600 (H = 525) has two
seeds among its unitary divisors, m₁ = n/5^2 = 1179832600464 (H = 217) and
m₂ = n/3 = 9831938337200 (H = 350).

Checked here (core Lean, no Mathlib; `decide`), with numbers given by their
prime-power lists and σ, d computed by the product formulas:
* `primes_ok`: the bases are prime (trial division);
* `n_val`, `n_harmonic`: the value of n and H(n) = 525;
* `seeds`: of all 2^8 unitary divisors of n, the harmonic ones > 1 are
  exactly m₁, m₂ and n; m₁ and m₂ divide neither each other, so each has
  no smaller harmonic unitary divisor > 1 (a unitary divisor of a unitary
  divisor of n is a unitary divisor of n).
Not checked here: that σ and d are given by the product formulas
(multiplicativity; Mathlib `ArithmeticFunction.isMultiplicative_sigma`).
-/

def isPrimeSmall (p : Nat) : Bool := 2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0)

abbrev PF := List (Nat × Nat)

def val (f : PF) : Nat := f.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
def sig (f : PF) : Nat := f.foldl (fun acc pe => acc * ((pe.1 ^ (pe.2 + 1) - 1) / (pe.1 - 1))) 1
def nd (f : PF) : Nat := f.foldl (fun acc pe => acc * (pe.2 + 1)) 1
def harmonic (f : PF) : Bool := (val f * nd f) % sig f == 0

def subsets : PF → List PF
  | [] => [[]]
  | x :: xs => (subsets xs).flatMap (fun s => [s, x :: s])

def nf : PF := [(2, 4), (3, 1), (5, 2), (7, 2), (19, 1), (31, 2), (83, 1), (331, 1)]

theorem primes_ok : nf.all (fun pe => isPrimeSmall pe.1) = true := by decide +kernel
theorem n_val : val nf = 29495815011600 := by decide
theorem n_harmonic : harmonic nf = true ∧ val nf * nd nf / sig nf = 525 := by decide

def seedVals : List Nat := [1179832600464, 9831938337200, 29495815011600]

theorem seeds :
    (subsets nf).all (fun s => (decide (val s > 1) && harmonic s) == seedVals.contains (val s)) = true ∧
    seedVals.all (fun m => (subsets nf).any (fun s => val s == m)) = true ∧
    9831938337200 % 1179832600464 ≠ 0 ∧ 1179832600464 % 9831938337200 ≠ 0 := by decide +kernel
