/-
OEIS A212843 (Coman). (1) Only Carmichael numbers ≡ 1 (mod 10) can have a prime
factor ≡ 1 (mod 10). (2) Every Carmichael number ≡ 1 (mod 10) whose prime
factors are all ≡ 1 (mod 10) can be written (30a+1)(30b+1)(30c+1),
(30a+11)(30b+11)(30c+11) or (30a+1)(30b+11)(30c+11); "in other words" none is
(30a+1)(30b+1)(30c+11).

(1) is true (10 | p - 1 | C - 1). (2) is true as stated. The "in other words"
sentence holds for Carmichael numbers with three prime factors (a prime factor
30a+1 forces 3 | C - 1, but the product is ≡ 11 (mod 30)), and fails when the
factors may be composite: C = 1044430736441 = 41*191*281*521*911 (all primes
≡ 11 mod 30, a Carmichael number) equals 7831 * 146401 * 911 with
7831 ≡ 146401 ≡ 1 and 911 ≡ 11 (mod 30).

Checked here (core Lean):
* `part1`: 10 | p - 1 and p - 1 | C - 1 give C ≡ 1 (mod 10) (C ≥ 1);
* `three_primes`: (30a+1)(30b+1)(30c+11) ≡ 2 (mod 3), so 3 ∤ C - 1;
* the counterexample: factorisation, primality of the five factors (trial
  division), Korselt's condition p - 1 | C - 1 for each, and the grouping.
Not checked here: Korselt's criterion in the necessary direction (if C is a
Carmichael number and p is a prime factor then p - 1 | C - 1, and C is
squarefree), which needs Fermat's little theorem and a primitive root mod p.
In the counterexample the sufficient direction of Korselt is used instead
(squarefree and p - 1 | C - 1 for all p | C implies Carmichael); also not
checked here.
-/

theorem part1 (C p : Nat) (hC : 1 ≤ C) (h10 : (p - 1) % 10 = 0) (hk : (C - 1) % (p - 1) = 0) :
    C % 10 = 1 := by
  have h1 : 10 ∣ p - 1 := Nat.dvd_of_mod_eq_zero h10
  have h2 : p - 1 ∣ C - 1 := Nat.dvd_of_mod_eq_zero hk
  have := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h1 h2)
  omega

theorem three_primes (a b c : Nat) : ((30 * a + 1) * (30 * b + 1) * (30 * c + 11)) % 3 = 2 := by
  rw [Nat.mul_mod, Nat.mul_mod (30 * a + 1)]
  have h1 : (30 * a + 1) % 3 = 1 := by omega
  have h2 : (30 * b + 1) % 3 = 1 := by omega
  have h3 : (30 * c + 11) % 3 = 2 := by omega
  rw [h1, h2, h3]

def C : Nat := 1044430736441
def fs : List Nat := [41, 191, 281, 521, 911]

/-- trial division: 2 ≤ n < 31^2 and no k with 2 ≤ k ≤ 30 divides n (so n is prime) -/
def isPrimeSmall (n : Nat) : Bool := 2 ≤ n && n < 961 && (List.range 31).all (fun k => k < 2 || n % k != 0 || n == k)

theorem product : fs.foldl (· * ·) 1 = C := by decide
theorem primes : fs.all isPrimeSmall = true := by decide
theorem korselt : fs.all (fun p => (C - 1) % (p - 1) == 0) = true := by decide
theorem mod30 : fs.all (fun p => p % 30 == 11) = true := by decide
theorem grouping : 41 * 191 = 7831 ∧ 281 * 521 = 146401 ∧ 7831 * 146401 * 911 = C ∧
    7831 % 30 = 1 ∧ 146401 % 30 = 1 ∧ 911 % 30 = 11 := by decide
