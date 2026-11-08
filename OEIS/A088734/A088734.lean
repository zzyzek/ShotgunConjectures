/-
OEIS A088734 ("First primes in p^p - 2m where p is prime and m = 1,2.."),
comment: "Conjecture: 2,3,5,7,11,13,17,19 are the only 1 and 2 digit primes in the
sequence."

The term for m is the first value x^x - 2m (x running over the primes 2, 3, 5, ...)
that is a (positive) prime.  For 2m = 3125 - q with q a prime, 10 <= q < 100, the
values 2^2 - 2m and 3^3 - 2m are negative and 5^5 - 2m = q is prime, so the term for
m is q.  Every two-digit prime is therefore a term (23 is already a(2) in the data).

Checked here (kernel evaluation, `decide`):
  * `A088734_97`: for 2m = 3028 the candidates from x = 2, 3 are not positive and
    x = 5 gives 97, a prime;
  * `A088734_two_digit`: the same for every prime q with 10 <= q < 100 and 2m = 3125 - q.
Not checked here: nothing beyond reading the definition (`val x M` is "x^x - M is a
positive prime", tested for x = 2, 3, 5 in order; primality by trial division).
-/

def isPrimeB (n : Nat) : Bool :=
  2 ≤ n && (List.range n).all (fun d => d < 2 || n % d != 0)

-- The candidate x^x - M when it is a positive prime.
--
def val (x M : Nat) : Option Nat :=
  if M < x ^ x ∧ isPrimeB (x ^ x - M) = true then some (x ^ x - M) else none

theorem A088734_97 : val 2 3028 = none ∧ val 3 3028 = none ∧ val 5 3028 = some 97 := by
  decide

theorem A088734_two_digit : ∀ q, q < 100 → 10 ≤ q → isPrimeB q = true →
    val 2 (3125 - q) = none ∧ val 3 (3125 - q) = none ∧ val 5 (3125 - q) = some q := by
  decide
