/-
OEIS A023402 / A081532.  Conjectures (OEIS wiki Talk:Conjectures/List):
A023402: a(n) = T(n+2, 3), the 3rd divisor of the smallest number with n+2
divisors; A081532: T(n, 3) = A023402(n-2) for n > 2.  Both false at the
same place: A023402(2) = 4 but T(4, 3) = 3.

Checked here (core Lean, `decide`):
* `t43`: 6 is the smallest number with exactly 4 divisors, and its divisors
  in increasing order are 1, 2, 3, 6, so T(4, 3) = 3.
* `a2`: A023402(2) = 4.  A023402 lists the last digits (read right to left)
  of a power of 2 whose last k digits are all 3s and 4s.  The two-digit
  candidates are 33, 34, 43, 44; 33 and 43 are odd, 34 ≡ 2 (mod 4) while
  4 ∣ 2^e for e ≥ 2 (`pow_mod4`), and 2^18 ends in 44.  So the last two
  digits are 4, 4 and a(2) = 4.
Not checked here: nothing beyond the reading of the definitions.
-/

def ndiv (m : Nat) : Nat := ((List.range (m + 1)).filter (fun d => d > 0 && m % d == 0)).length

def divisors (m : Nat) : List Nat := (List.range (m + 1)).filter (fun d => d > 0 && m % d == 0)

theorem t43 : (List.range 6).all (fun m => ndiv m != 4) = true ∧ ndiv 6 = 4 ∧
    divisors 6 = [1, 2, 3, 6] := by decide

theorem pow_mod4 (e : Nat) : 2 ^ (e + 2) % 4 = 0 := by
  induction e with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem a2 : 2 ^ 18 % 100 = 44 ∧ 34 % 4 = 2 ∧ 33 % 2 = 1 ∧ 43 % 2 = 1 := by decide
