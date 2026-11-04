/-
OEIS A000040 (primes). Conjecture (OEIS wiki Talk:Conjectures/List, A000040
line 16): for n > 2, prime(n) = (6 f + (-1)^f - 3)/2 where
f = floor(prime(n)/3) + 1.  True (trivial).

Checked here (core Lean, full statement):
* `formula_eq`: for every natural p with p mod 6 ∈ {1, 5} the formula
  returns p.  The term (-1)^f is written as a case split on the parity of f
  (f even: (6f + 1 - 3)/2, f odd: (6f - 1 - 3)/2).
* `prime_mod6`: every p > 3 whose only divisors are 1 and p has
  p mod 6 ∈ {1, 5}.
* `main`: the conjecture for every prime p > 3 (n > 2 means p ≥ 5).
Not checked here: nothing; "prime" is the divisor definition `IsPrime`.
-/

def formula (p : Nat) : Nat :=
  if (p / 3 + 1) % 2 = 0 then (6 * (p / 3 + 1) + 1 - 3) / 2
  else (6 * (p / 3 + 1) - 1 - 3) / 2

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem formula_eq (p : Nat) (h : p % 6 = 1 ∨ p % 6 = 5) : formula p = p := by
  unfold formula
  split <;> omega

theorem prime_mod6 (p : Nat) (hp : IsPrime p) (h3 : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have n2 : ¬ (2 ∣ p) := by
    intro hd
    rcases hp.2 2 hd with h | h <;> omega
  have n3 : ¬ (3 ∣ p) := by
    intro hd
    rcases hp.2 3 hd with h | h <;> omega
  omega

theorem main (p : Nat) (hp : IsPrime p) (h3 : 3 < p) : formula p = p :=
  formula_eq p (prime_mod6 p hp h3)
