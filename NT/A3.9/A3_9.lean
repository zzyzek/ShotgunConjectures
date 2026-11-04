/-
NT-A3.9 (Guy, UPINT 3rd ed., A3): with p(k) the smallest prime whose decimal
digits sum to k, "is p(k) ≡ 99 (mod 100) for k > 38, and ≡ 999 (mod 1000)
for k > 59?"  No: p(86) = 6999999989.

Checked here (core Lean, no Mathlib; `decide`):
* `digits_86`: 6999999989 has digit sum 86, and is ≡ 89 (mod 100), ≡ 989 (mod 1000);
* `smaller_composite`: the eight smaller integers with digit sum 86
  (5999999999, 6899999999, ..., 6999999899) each have a proper factor.
Not checked here:
* that these eight are all the integers below 6999999989 with digit sum 86
  (any such number has 10 digits with digit deficit 90 − 86 = 4 from 9999999999;
  leading digit 5 forces 5999999999, leading digit 6 leaves one more unit of
  deficit in one of nine places; see README);
* that 6999999989 is prime (trial division to 83666 and Miller–Rabin in
  certificate/a39_check.py; kernel trial division timed out at 300 s).
-/

/-- decimal digit sum, with fuel (enough for numbers below 10^fuel) -/
def ds : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => n % 10 + ds f (n / 10)

theorem digits_86 : ds 11 6999999989 = 86 ∧ 6999999989 % 100 = 89 ∧ 6999999989 % 1000 = 989 := by
  decide

def smaller : List (Nat × Nat) :=
  [(5999999999, 7), (6899999999, 6089), (6989999999, 827), (6998999999, 19),
   (6999899999, 61), (6999989999, 31), (6999998999, 7), (6999999899, 3011)]

theorem smaller_composite :
    smaller.all (fun e => ds 11 e.1 == 86 && e.1 < 6999999989 && 1 < e.2 && e.2 < e.1 && e.1 % e.2 == 0) = true := by
  decide
