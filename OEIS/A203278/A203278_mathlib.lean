import Mathlib
import OpenProblemsLib.ShevelevFactorial

/-
OEIS A203278 (V. Shevelev): a(n) = sum_(m=0..n) C^(2)(n,m), the row sums of A202941.
Conjecture: a((p-1)/2) = 2 (mod p) for every odd prime p.
Main theorem `A203278_main`: for an odd prime p, every integer N equal to a((p-1)/2) satisfies
p | N - 2.

Definitions (library `OpenProblemsLib.ShevelevFactorial`).
* `shevQ t m` = Q^(t)_m: `shevQ_zero` (Q_0 = 1) and `shevQ_succ_eval`
  (Q_(m+1)(n) = sum_(i=1..n) i^t Q_m(i) for every natural n); `shevQ_unique`: any family of
  rational polynomials with these two properties equals `shevQ t`.
* `shevFact t n` = n!^(t) = lcm of the denominators of the coefficients of Q^(t)_n.
* `shevBinom t n m` = C^(t)(n,m) = n!^(t) / (m!^(t) (n-m)!^(t)) (a rational number).
Route: `shevelev_row` (Newton's identity m Q_m = sum_(a+b=m, b>=1) Q_a S_(tb); S_k is p-integral
for 1 <= k <= 2p-3, k != p-1 (von Staudt-Clausen); S_(p-1), S_(2p-2) are not (sum of i^k over
i <= p is -1 mod p); S_(2p-1) is not (top coefficient 1/(2p))). This file checks the row-index
arithmetic (omega) and applies it.
Not checked here: the reading of "multiple of p" for the (rational) entries as v_p >= 1, and of
"= 2 (mod p)" for the row sum as: every integer equal to the row sum is 2 mod p.
Axioms: propext, Classical.choice, Quot.sound.
-/

namespace A203278

open OpenProblemsLib.ShevelevFactorial

/-- Row sums: `a n = ∑_(m=0..n) C^(2)(n, m)`. -/
noncomputable def a (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), shevBinom 2 n m

theorem A203278_main (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (N : ℤ)
    (hN : (N : ℚ) = a ((p - 1) / 2)) : (p : ℤ) ∣ N - 2 := by
  have := Fact.mk hp
  have h2 := hp.two_le
  have ho : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hodd
    · exact h
  exact (shevelev_row (p := p) 2 ((p - 1) / 2) (by norm_num) (by omega)
    (fun s _ hs => by omega) (by left; omega)).2.2.2 N hN

