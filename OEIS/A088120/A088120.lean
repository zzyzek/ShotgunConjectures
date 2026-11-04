/-
OEIS A088120 (smallest prime of the form a(a+d)···(a+(n-1)d) + d, a, d ≥ 1).
Conjecture (2): the common difference is 1 except for n = 4 and 5 (d = 2).
False at n = 12: a(12) = 1·3·5···23 + 2 = 316234143227 (d = 2).

Checked here (core Lean, `decide`):
* `d1_composite`: the d = 1 values below W = 316234143227, i.e. k(k+1)···(k+11) + 1
  for k = 1..4, have explicit proper factors.
* `bounds`: W = 1·3···23 + 2, and the next candidates are above W:
  k = 5 with d = 1, a = 2 with d = 2, a = 1 with d = 3.
Not checked here: primality of W (sympy/PARI; a 12-digit number) and the
monotonicity of the product in a and d (so the listed candidates are all
values ≤ W).
-/

def f (n a d : Nat) : Nat := ((List.range n).map (fun i => a + i * d)).foldl (· * ·) 1 + d

def W : Nat := 316234143227

theorem d1_composite :
    f 12 1 1 = 479001601 ∧ 479001601 = 13 * 36846277 ∧
    f 12 2 1 = 6227020801 ∧ 6227020801 = 83 * 75024347 ∧
    f 12 3 1 = 43589145601 ∧ 43589145601 = 31 * 1406101471 ∧
    f 12 4 1 = 217945728001 ∧ 217945728001 = 32009 * 6808889 := by decide

theorem bounds : f 12 1 2 = W ∧ W < f 12 5 1 ∧ W < f 12 2 2 ∧ W < f 12 1 3 := by decide
