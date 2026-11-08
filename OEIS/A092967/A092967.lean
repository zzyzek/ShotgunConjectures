/-
OEIS A092967: largest prime of the form s + 1, s squarefree with prime factors
< n (the data use <= n). Conjecture in the entry: a(n) - 1 has prime(n) - 1 divisors.
False at n = 4: under either reading the admissible s are 1, 2, 3, 6 (products of
subsets of {2, 3}), the primes among s + 1 are 2, 3, 7, so a(4) = 7; a(4) - 1 = 6 has
4 divisors, while prime(4) - 1 = 6.

Checked here: the list of s + 1 values for the subsets of {2, 3}, which of them are
prime, their maximum, the divisor count of 6, and that 7 is the 4th prime.
Not checked here: that the subsets of {2, 3} are exactly the squarefree numbers with
prime factors <= 4 (immediate from the definition).
-/

def isPrimeTD (p : Nat) : Bool :=
  2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0)

/-- s + 1 for s = 1, 2, 3, 2*3. -/
def cands : List Nat := [1 + 1, 2 + 1, 3 + 1, 2 * 3 + 1]

def a4 : Nat := ((cands.filter isPrimeTD).foldl max 0)

def numDivisors (m : Nat) : Nat := ((List.range (m + 1)).filter (fun d => 1 ≤ d && m % d == 0)).length

theorem primes_below_5 : (List.range 5).filter isPrimeTD = [2, 3] := by decide
theorem a4_eq : a4 = 7 := by decide
theorem a4_prime : isPrimeTD a4 = true := by decide
theorem tau_6 : numDivisors (a4 - 1) = 4 := by decide
theorem fourth_prime : (List.range 8).filter isPrimeTD = [2, 3, 5, 7] := by decide
theorem A092967_conjecture_false_n4 : numDivisors (a4 - 1) ≠ 7 - 1 := by decide
