/-
NT-B2.3 (Guy, UPINT 3rd ed., B2, Kravitz): "there are no n whose abundance
σ(n) − 2n is an odd square".  False; the book itself reports Cohen's
counterexamples.  Smallest: n = 2^2 · 7^2 · 53^2 = 550564, σ(n) − 2n = 203^2.

Checked here (core Lean, no Mathlib; `decide`):
* `b2_3_value`: 2^2·7^2·53^2 = 550564; with σ(p^e) = (p^{e+1} − 1)/(p − 1)
  the product σ(4)σ(49)σ(2809) = 7·57·2863 = 1142337 and
  1142337 − 2·550564 = 41209 = 203^2 (odd);
* `prime_53`: 53 is prime (2 and 7 are evident).
Not checked here: multiplicativity of σ (standard; Mathlib
`ArithmeticFunction.isMultiplicative_sigma`).
-/

def sigmaPP (p e : Nat) : Nat := ((List.range (e + 1)).map (fun i => p ^ i)).foldl (· + ·) 0

theorem b2_3_value :
    2 ^ 2 * 7 ^ 2 * 53 ^ 2 = 550564 ∧
    sigmaPP 2 2 * sigmaPP 7 2 * sigmaPP 53 2 = 1142337 ∧
    1142337 - 2 * 550564 = 203 ^ 2 ∧ 203 % 2 = 1 := by decide

theorem prime_53 : ∀ d < 53, d < 2 ∨ 53 % d ≠ 0 := by decide
