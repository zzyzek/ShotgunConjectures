/-
OEIS A088082: indices n with A088081(n+1) > A088081(n), where A088081(n) is the
smallest prime P such that for every r = 1..n there are primes p < p' <= P with
r ∣ p' - p. Conjecture (entry): n + 1 is a prime.

False: A088081 = 3, 5, 5, 7, 7, 11, ... so n = 3 (n+1 = 4) and n = 5 (n+1 = 6) are
terms; n = 32 (A088081(32) = 67 < A088081(33) = 71, n+1 = 33) is another.

Checked here (by `decide`): `a 3 = 5`, `a 4 = 7`, `a 5 = 7`, `a 6 = 11`, `a 32 = 67`,
`a 33 = 71`, where `a n` is the least P < 200 that is prime and satisfies the
condition for r = 1..n (`a` returns 0 if none; the values found are below 200, so
`a n` is A088081(n)).
Not checked here: nothing else is needed for the counterexamples.
-/

def isPrime (p : Nat) : Bool := 2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0)

/-- some pair of primes p < p' <= P has r ∣ p' - p -/
def good (P r : Nat) : Bool :=
  let ps := (List.range (P + 1)).filter isPrime
  ps.any (fun p => ps.any (fun q => p < q && (q - p) % r == 0))

def ok (P n : Nat) : Bool := isPrime P && (List.range n).all (fun i => good P (i + 1))

/-- A088081(n): least prime P (searched below 200) with the property for r = 1..n. -/
def a (n : Nat) : Nat := ((List.range 200).find? (fun P => ok P n)).getD 0

theorem a3 : a 3 = 5 := by decide
theorem a4 : a 4 = 7 := by decide
theorem a5 : a 5 = 7 := by decide
theorem a6 : a 6 = 11 := by decide
theorem a32 : a 32 = 67 := by decide
theorem a33 : a 33 = 71 := by decide

theorem counterexample_3 : a 3 < a 4 ∧ isPrime 4 = false := by decide
theorem counterexample_5 : a 5 < a 6 ∧ isPrime 6 = false := by decide
theorem counterexample_32 : a 32 < a 33 ∧ isPrime 33 = false := by decide
