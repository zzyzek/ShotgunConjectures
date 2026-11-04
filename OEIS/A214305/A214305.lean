/-
OEIS A214305 (Poulet numbers with two prime factors). Conjecture 2 (Coman): any
Poulet number p2 divisible by d can be written (p1 - d) n + d if a smaller
Poulet number p1 with two prime factors is divisible by d. False.

* d any common prime: p1 = 341 = 11*31, p2 = 561 = 3*11*17, d = 11:
  561 - 11 = 550 is not a multiple of 330.
* d the largest prime factor of p1 (as in conjectures 1 and 3): p1 = 23377 =
  97*241, p2 = 34945 = 5*29*241, d = 241: 34704 is not a multiple of 23136.
  (23377 is the only two-factor Poulet number below 34945 with largest factor
  241, by the Feitsma-Galway table; so this fails under every reading of which
  p1 is meant.) Also p1 = 5461 = 43*127, p2 = 55245 = 3*5*29*127.

Checked here (core Lean, `decide`; `Nat.pow` and `%` are kernel-accelerated):
the Fermat condition 2^(n-1) ≡ 1 (mod n), the factorisations, primality of
the factors (trial division), and the failed divisibilities.
Not checked here: that 23377 and 5461 are the only qualifying p1 below 34945
and 55245 (table scan in certificate/a214305_strict.py), which only matters
for the "some p1" reading. The "infinitely many" conjectures 1 and 3 are not
addressed.
-/

def poulet (n : Nat) : Bool := 2 ^ (n - 1) % n == 1
/-- trial division: 2 ≤ n < 16^2 and no k with 2 ≤ k ≤ 15, k ≠ n, divides n (so n is prime) -/
def isPrimeSmall (n : Nat) : Bool := 2 ≤ n && n < 256 && (List.range 16).all (fun k => k < 2 || n % k != 0 || n == k)

theorem poulets : [341, 561, 23377, 34945, 5461, 55245].all poulet = true := by decide +kernel
theorem factors : 11 * 31 = 341 ∧ 3 * 11 * 17 = 561 ∧ 97 * 241 = 23377 ∧ 5 * 29 * 241 = 34945 ∧
    43 * 127 = 5461 ∧ 3 * 5 * 29 * 127 = 55245 := by decide
theorem primes : [3, 5, 11, 17, 29, 31, 43, 97, 127, 241].all isPrimeSmall = true := by decide
theorem fail_11 : (561 - 11) % (341 - 11) ≠ 0 := by decide
theorem fail_241 : (34945 - 241) % (23377 - 241) ≠ 0 := by decide
theorem fail_127 : (55245 - 127) % (5461 - 127) ≠ 0 := by decide
