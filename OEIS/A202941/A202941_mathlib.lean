import Mathlib
import OpenProblemsLib.ShevelevFactorial

/-
OEIS A202941 (V. Shevelev): triangle T(n,m) = C^(2)(n,m), rows n >= 0, 0 <= m <= n.
Conjecture: if p is an odd prime, row (p-1)/2 contains two 1's and (p-3)/2 multiples of p.
Main theorem `A202941_main`: for an odd prime p and r = (p-1)/2, T(r,0) = T(r,r) = 1 and every
T(r,m) with 0 < m < r has p-adic valuation >= 1 (so it is not 1).

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

namespace A202941

open OpenProblemsLib.ShevelevFactorial

/-- The triangle: `T n m = C^(2)(n, m)`. -/
noncomputable def T (n m : ℕ) : ℚ := shevBinom 2 n m

theorem A202941_main (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    T ((p - 1) / 2) 0 = 1 ∧ T ((p - 1) / 2) ((p - 1) / 2) = 1 ∧
    ∀ m, 0 < m → m < (p - 1) / 2 →
      1 ≤ padicValRat p (T ((p - 1) / 2) m) ∧ T ((p - 1) / 2) m ≠ 1 := by
  have := Fact.mk hp
  have h2 := hp.two_le
  have ho : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hodd
    · exact h
  obtain ⟨h0, h1, h3, -⟩ := shevelev_row (p := p) 2 ((p - 1) / 2) (by norm_num) (by omega)
    (fun s _ hs => by omega) (by left; omega)
  exact ⟨h0, h1, h3⟩

