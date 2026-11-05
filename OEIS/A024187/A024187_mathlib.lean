/-
OEIS A024187, Mathlib proof of R. Stephan's conjecture "essentially the same as A001711".

A024187(n) (offset 1) = n-th elementary symmetric function of 3, 4, ..., n+3
  (`A024187`: sum over n-element subsets t of {0..n} of the product of (i+3), i in t).
A001711(n) (offset 0) = generalized Stirling number [n+4, 4]_3, read as in the entry
  (P. Hadjicostas): a(n) = R_{n+1}^1(-3, -1) = [x^1] Prod_{r=0..n} (x + 3 + r)
  (`A001711`: coefficient 1 of that polynomial in ℕ[X]).

Main theorem `A024187_conjecture`: A024187 n = A001711 n for every n (so the two
sequences agree term by term on n ≥ 1, A001711 having the extra leading term a(0) = 1).
Proof: Vieta's formula `Finset.prod_X_add_C_coeff`.
Supporting: `A001711_rec` (a(n+1) = (n+4) a(n) + 3·4···(n+3)), `A001711_data`
(a(0..10) against the entry).

Not checked in Lean: that [n+4,4]_3 in the entry's name means the coefficient above.
That reading is the entry's own formula (Hadjicostas, Mitrinovic numbers R_n^m(a,b)), and
it agrees with the r-Stirling numbers of Broder ([n,k]_r = [x^k] x^r (x+r)...(x+n-1)).
-/
import Mathlib

open Polynomial Finset

/-- A024187(n): the n-th elementary symmetric function of 3, 4, ..., n+3. -/
def A024187 (n : ℕ) : ℕ := ∑ t ∈ (range (n + 1)).powersetCard n, ∏ i ∈ t, (i + 3)

/-- A001711(n) = [x^1] Prod_{r=0..n} (x + 3 + r). -/
noncomputable def A001711 (n : ℕ) : ℕ := (∏ r ∈ range (n + 1), (X + C (r + 3))).coeff 1

theorem A024187_conjecture (n : ℕ) : A024187 n = A001711 n := by
  unfold A024187 A001711
  rw [Finset.prod_X_add_C_coeff _ _ (by simp), card_range, Nat.add_sub_cancel]

/-- (a(n), 3·4···(n+3)) computed by the recurrence. -/
def A001711_pair : ℕ → ℕ × ℕ
  | 0 => (1, 3)
  | n + 1 => ((n + 4) * (A001711_pair n).1 + (A001711_pair n).2, (A001711_pair n).2 * (n + 4))

theorem A001711_pair_eq (n : ℕ) :
    A001711 n = (A001711_pair n).1 ∧
      (∏ r ∈ range (n + 1), (X + C (r + 3) : ℕ[X])).coeff 0 = (A001711_pair n).2 := by
  induction n with
  | zero =>
    simp [A001711, A001711_pair]
  | succ n ih =>
    obtain ⟨h1, h0⟩ := ih
    unfold A001711 at h1 ⊢
    rw [prod_range_succ, mul_add, coeff_add, coeff_add, mul_comm _ X, coeff_X_mul, coeff_X_mul_zero,
      coeff_mul_C, coeff_mul_C, h1, h0]
    simp only [A001711_pair]
    constructor <;> ring

theorem A001711_pair_snd (n : ℕ) : (A001711_pair n).2 = ∏ r ∈ range (n + 1), (r + 3) := by
  induction n with
  | zero => simp [A001711_pair]
  | succ n ih => rw [prod_range_succ, ← ih]; simp only [A001711_pair]

/-- a(n+1) = (n+4) a(n) + 3·4···(n+3). -/
theorem A001711_rec (n : ℕ) :
    A001711 (n + 1) = (n + 4) * A001711 n + ∏ r ∈ range (n + 1), (r + 3) := by
  rw [(A001711_pair_eq (n + 1)).1, (A001711_pair_eq n).1, ← A001711_pair_snd]
  simp only [A001711_pair]

theorem A001711_data :
    (List.range 11).map (fun n => (A001711_pair n).1) =
      [1, 7, 47, 342, 2754, 24552, 241128, 2592720, 30334320, 383970240, 5231113920] := by
  decide
