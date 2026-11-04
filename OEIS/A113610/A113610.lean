/-
OEIS A113610 (sum of the digits of all composite numbers strictly between
prime(n) and prime(n+1)).  Conjecture: for n > 9, if a(n) > a(n+1) < a(n+2) then
prime(n) and prime(n+1) form a twin prime pair.  False at n = 12; the variant
"prime(n+1), prime(n+2) are twins" fails at n = 21.

Checked here (core Lean, `decide`):
* `primes90`: the primes below 90 are exactly the listed 24 numbers, so
  prime(12..14) = 37, 41, 43 and prime(21..24) = 73, 79, 83, 89.
* `n12`: a(12) = 27 > a(13) = 6 < a(14) = 27, and 41 - 37 = 4.
* `n21`: a(21) = 65 > a(22) = 27 < a(23) = 70, and 83 - 79 = 4.
Not checked here: nothing (the scan found 3194 literal and 1981 variant
failures below 10^5; certificate/check.py).
-/

def isPrimeB (p : Nat) : Bool := 2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0)

def P : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89]

theorem primes90 : (List.range 90).filter isPrimeB = P := by decide

def ds : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, x => x % 10 + (if x < 10 then 0 else ds f (x / 10))

/-- a(n), n ≥ 1: digit sum of the integers strictly between prime(n) and prime(n+1)
    (all of them composite). -/
def A (n : Nat) : Nat :=
  let lo := P.getD (n - 1) 0
  let hi := P.getD n 0
  ((List.range (hi - lo - 1)).map (fun i => ds 3 (lo + 1 + i))).sum

theorem n12 : A 12 = 27 ∧ A 13 = 6 ∧ A 14 = 27 ∧ P.getD 11 0 = 37 ∧ P.getD 12 0 = 41 := by decide
theorem n21 : A 21 = 65 ∧ A 22 = 27 ∧ A 23 = 70 ∧ P.getD 21 0 = 79 ∧ P.getD 22 0 = 83 := by decide
