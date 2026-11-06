import Mathlib
import OpenProblemsLib.ShevelevFactorial

/-
OEIS A203498 (V. Shevelev): a(n) = sum_(m=0..n) C^(3)(n,m), the row sums of A203484.
Conjecture: a((p-1)/3) = 2 (mod p) for primes p = 1 (mod 3), a((2p-1)/3) = 2 (mod p) for
primes p = 2 (mod 3).
Main theorem `A203498_main`: for a prime p and r = (p-1)/3 (p = 1 mod 3) or r = (2p-1)/3
(p = 2 mod 3), every integer N equal to a(r) satisfies p | N - 2.

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

namespace A203498

open OpenProblemsLib.ShevelevFactorial

/-- Row sums: `a n = ∑_(m=0..n) C^(3)(n, m)`. -/
noncomputable def a (n : ℕ) : ℚ := ∑ m ∈ Finset.range (n + 1), shevBinom 3 n m

theorem A203498_main (p : ℕ) (hp : p.Prime) (r : ℕ)
    (hr : (p % 3 = 1 ∧ r = (p - 1) / 3) ∨ (p % 3 = 2 ∧ r = (2 * p - 1) / 3))
    (N : ℤ) (hN : (N : ℚ) = a r) : (p : ℤ) ∣ N - 2 := by
  have := Fact.mk hp
  have h2 := hp.two_le
  exact (shevelev_row (p := p) 3 r (by norm_num) (by omega)
    (fun s _ hs => by omega) (by omega)).2.2.2 N hN

