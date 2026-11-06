/-
OEIS A131439 (offset 1): inverse binomial transform of A131438 "assuming zero
offset in both sequences", where A131438(n) = (2+n) 2^n - 2 - 3n (offset 1).
Conjecture (entry comment): the sequence is 1, 7 followed by 4k + 14
(k = 0, 1, 2, ...), and its own inverse binomial transform is
1, 6, 1, -4, 7, -10, 13, -16, ...

Definitions.  `A131438 n` is the closed form above; `b k = A131438 (k+1)` (zero
offset, `b_eq`); `invBinom f m = Σ_{k ≤ m} (-1)^(m-k) C(m,k) f k`;
`A131439 n = invBinom b (n-1)`; `c m = A131439 (m+1)`.

Main theorems.
* `A131439_one`, `A131439_two`, `A131439_closed`: A131439 = 1, 7, then
  A131439 n = 4n + 2 for n ≥ 3 (= 4k + 14 with k = n - 3).
* `invBinom_c_zero`, `invBinom_c_one`, `invBinom_c`: the inverse binomial
  transform of A131439 (zero offset) is 1, 6, then (-1)^m (3m - 5) for m ≥ 2.

Proof.  invBinom f m is the m-th forward difference of f at 0 (Mathlib
`fwdDiff_iter_eq_sum_shift`).  b k = (2k+6) 2^k - 3k - 5, its second difference
is (2k+14) 2^k, and the difference of (2k+A) 2^k is (2k+A+4) 2^k.

Not checked in this file: agreement with the OEIS data beyond n ≤ 2
(certificate/check.py compares 200 terms).
-/
import Mathlib

open Finset

/-- OEIS A131438 (offset 1). -/
def A131438 (n : ℕ) : ℤ := (2 + (n : ℤ)) * 2 ^ n - 2 - 3 * (n : ℤ)

/-- A131438 with zero offset: `b k = A131438 (k+1) = (k+3) 2^(k+1) - 2 - 3(k+1)`. -/
def b (k : ℕ) : ℤ := ((k : ℤ) + 3) * 2 ^ (k + 1) - 2 - 3 * ((k : ℤ) + 1)

theorem b_eq (k : ℕ) : b k = A131438 (k + 1) := by
  simp only [b, A131438]
  push_cast
  ring

/-- Inverse binomial transform (zero offset). -/
def invBinom (f : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ k ∈ range (m + 1), (-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) * f k

/-- OEIS A131439 (offset 1): `A131439 (m+1) = invBinom b m`. -/
def A131439 (n : ℕ) : ℤ := invBinom b (n - 1)

theorem invBinom_eq_fwdDiff (f : ℕ → ℤ) (m : ℕ) : invBinom f m = ((fwdDiff 1)^[m] f) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold invBinom
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [smul_eq_mul]

/-- `g A k = (2k + A) 2^k`. -/
def g (A : ℤ) (k : ℕ) : ℤ := (2 * (k : ℤ) + A) * 2 ^ k

theorem fwdDiff_g (A : ℤ) : fwdDiff 1 (g A) = g (A + 4) := by
  funext k
  simp only [fwdDiff, g]
  push_cast
  ring

theorem fwdDiff_b_two : (fwdDiff 1)^[2] b = g 14 := by
  funext k
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, fwdDiff, b, g]
  push_cast
  ring

theorem fwdDiff_b_iter (j : ℕ) : (fwdDiff 1)^[j + 2] b = g (14 + 4 * j) := by
  induction j with
  | zero => simpa using fwdDiff_b_two
  | succ j ih =>
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, Function.iterate_succ_apply', ih, fwdDiff_g]
    congr 1

/-- The conjecture: A131439 n = 4n + 2 for n ≥ 3, i.e. 14, 18, 22, ... -/
theorem A131439_closed (n : ℕ) (hn : 3 ≤ n) : A131439 n = 4 * (n : ℤ) + 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  unfold A131439
  rw [show j + 3 - 1 = j + 2 by omega, invBinom_eq_fwdDiff, fwdDiff_b_iter]
  simp [g]
  ring

theorem A131439_one : A131439 1 = 1 := by decide
theorem A131439_two : A131439 2 = 7 := by decide

/-- Zero-offset A131439: `c m = A131439 (m+1)`. -/
def c (m : ℕ) : ℤ := A131439 (m + 1)

theorem c_eq (m : ℕ) : c m = 4 * (m : ℤ) + 6 - (if m = 1 then 3 else 0) - (if m = 0 then 5 else 0) := by
  rcases m with _ | _ | m
  · decide
  · decide
  · unfold c
    rw [A131439_closed _ (by omega)]
    simp
    ring

theorem fwdDiff_iter_zero (m : ℕ) : (fwdDiff 1)^[m] (0 : ℕ → ℤ) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    funext k
    simp [fwdDiff]

theorem invBinom_linear (m : ℕ) : invBinom (fun k => 4 * (k : ℤ) + 6) (m + 2) = 0 := by
  rw [invBinom_eq_fwdDiff, Function.iterate_succ_apply, Function.iterate_succ_apply]
  have h2 : fwdDiff 1 (fwdDiff 1 (fun k : ℕ => 4 * (k : ℤ) + 6)) = 0 := by
    funext k
    simp only [fwdDiff, Pi.zero_apply]
    push_cast
    ring
  rw [h2, fwdDiff_iter_zero]
  rfl

theorem invBinom_delta (i : ℕ) (v : ℤ) (m : ℕ) (hi : i ≤ m) :
    invBinom (fun k => if k = i then v else 0) m = (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * v := by
  unfold invBinom
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, show i < m + 1 by omega, ite_true]

/-- The second comment: the inverse binomial transform of A131439 is 1, 6, 1, -4, 7, -10, ...,
that is `(-1)^m (3m - 5)` for `m ≥ 2`. -/
theorem invBinom_c (m : ℕ) (hm : 2 ≤ m) : invBinom c m = (-1 : ℤ) ^ m * (3 * (m : ℤ) - 5) := by
  have hc : c = fun k : ℕ => (4 * (k : ℤ) + 6) - (if k = 1 then 3 else 0) - (if k = 0 then 5 else 0) := by
    funext k; exact c_eq k
  have lin : ∀ f g : ℕ → ℤ, invBinom (fun k => f k - g k) m = invBinom f m - invBinom g m := by
    intro f g
    unfold invBinom
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hc, lin (fun k => (4 * (k : ℤ) + 6) - (if k = 1 then 3 else 0)) (fun k => if k = 0 then 5 else 0),
    lin (fun k => 4 * (k : ℤ) + 6) (fun k => if k = 1 then 3 else 0),
    invBinom_delta 1 3 m (by omega), invBinom_delta 0 5 m (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  rw [invBinom_linear]
  simp only [Nat.choose_one_right, Nat.choose_zero_right, show j + 2 - 1 = j + 1 by omega,
    Nat.sub_zero]
  push_cast
  ring

theorem invBinom_c_zero : invBinom c 0 = 1 := by decide
theorem invBinom_c_one : invBinom c 1 = 6 := by decide
