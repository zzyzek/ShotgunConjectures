import Mathlib

/-
OEIS A229136 (offset 1): number of solutions to Sum_{i=1..n} x_i^2 == 1 (mod 4)
with x_i in 0..3.  Conjecture (entry): a(n) = A131885(n) * 2^(n-1) for n >= 1
(exponent as corrected by P. Hadjicostas, Dec 20 2019, who also proved it in
the entry via the recurrences of A330619).  The scan record quotes the form
a(n) = A131885(n) * 2^n, which fails at n = 1.

Definitions.  `cnt n r` counts `x : Fin n → Fin 4` with (Σ x_i^2) % 4 = r;
`A229136 n = cnt n 1`; `A131885` by its defining recurrence (a(0..3) = 1, 2, 4,
6, a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3)).

Main theorems.
* `A229136_formula`: (A229136 n : ℤ) = A131885 n * 2^(n-1) for n ≥ 1.
* `scan_form_false`: the 2^n form fails at n = 1.

Route.  `cnt_succ`: splitting off x_0 (squares of 0, 1, 2, 3 are 0, 1, 0, 1
mod 4), cnt(n+1, r) = 2 cnt(n, r) + 2 cnt(n, r-1).  `alt`: the alternating sum
over residues vanishes for n ≥ 1.  `rec1`: hence the residue-1 count obeys
c(n+4) = 8c(n+3) - 24c(n+2) + 32c(n+1); induction from c(1..3) = 2, 8, 24.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py counts by brute force).
-/

namespace OEIS

/-- Number of `x : Fin n → Fin 4` (entries 0..3) with `∑ x_i^2 ≡ r (mod 4)`. -/
def cnt (n r : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 4 => (∑ i, ((x i : ℕ)) ^ 2) % 4 = r)).card

/-- A229136(n): solutions of `∑_{i=1..n} x_i^2 ≡ 1 (mod 4)` with `x_i ∈ 0..3`. -/
def A229136 (n : ℕ) : ℕ := cnt n 1

/-- A131885: a(0..3) = 1, 2, 4, 6, a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) for n ≥ 4. -/
def A131885 : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | (n + 4) => 4 * A131885 (n + 3) - 6 * A131885 (n + 2) + 4 * A131885 (n + 1)

theorem cnt_succ (n r : ℕ) (hr : r < 4) :
    cnt (n + 1) r = 2 * cnt n r + 2 * cnt n ((r + 3) % 4) := by
  simp only [cnt, Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_four]
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have e0 : ∀ s : ℕ, ((((0 : Fin 4) : ℕ)) ^ 2 + s) % 4 = r ↔ s % 4 = r := by
    intro s; simp
  have e1 : ∀ s : ℕ, ((((1 : Fin 4) : ℕ)) ^ 2 + s) % 4 = r ↔ s % 4 = (r + 3) % 4 := by
    intro s; simp; omega
  have e2 : ∀ s : ℕ, ((((2 : Fin 4) : ℕ)) ^ 2 + s) % 4 = r ↔ s % 4 = r := by
    intro s; simp
  have e3 : ∀ s : ℕ, ((((3 : Fin 4) : ℕ)) ^ 2 + s) % 4 = r ↔ s % 4 = (r + 3) % 4 := by
    intro s; simp; omega
  simp only [e0, e1, e2, e3]
  ring

/-- Counts as integers, with the four residue recurrences. -/
def c (n r : ℕ) : ℤ := cnt n r

theorem c0 (n : ℕ) : c (n + 1) 0 = 2 * c n 0 + 2 * c n 3 := by
  simp only [c]; rw [cnt_succ n 0 (by omega)]; push_cast; rfl
theorem c1 (n : ℕ) : c (n + 1) 1 = 2 * c n 1 + 2 * c n 0 := by
  simp only [c]; rw [cnt_succ n 1 (by omega)]; push_cast; rfl
theorem c2 (n : ℕ) : c (n + 1) 2 = 2 * c n 2 + 2 * c n 1 := by
  simp only [c]; rw [cnt_succ n 2 (by omega)]; push_cast; rfl
theorem c3 (n : ℕ) : c (n + 1) 3 = 2 * c n 3 + 2 * c n 2 := by
  simp only [c]; rw [cnt_succ n 3 (by omega)]; push_cast; rfl

theorem c_zero (r : ℕ) : c 0 r = if r = 0 then 1 else 0 := by
  simp only [c, cnt]
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  · simp only [show r ≠ 0 by omega, ite_false]; simp; omega

/-- Even minus odd residues cancel after one step. -/
theorem alt (n : ℕ) : c (n + 1) 0 - c (n + 1) 1 + c (n + 1) 2 - c (n + 1) 3 = 0 := by
  rw [c0, c1, c2, c3]; ring

theorem rec1 (n : ℕ) :
    c (n + 4) 1 = 8 * c (n + 3) 1 - 24 * c (n + 2) 1 + 32 * c (n + 1) 1 := by
  have h := alt n
  show c (n + 1 + 1 + 1 + 1) 1
    = 8 * c (n + 1 + 1 + 1) 1 - 24 * c (n + 1 + 1) 1 + 32 * c (n + 1) 1
  simp only [c0, c1, c2, c3] at h ⊢
  linear_combination 8 * h

/-- The conjecture of the entry (as corrected by P. Hadjicostas):
a(n) = A131885(n) * 2^(n-1) for n ≥ 1. -/
theorem A229136_formula (n : ℕ) (hn : 1 ≤ n) :
    (A229136 n : ℤ) = A131885 n * 2 ^ (n - 1) := by
  have base1 : c 1 1 = 2 := by rw [c1, c_zero, c_zero]; simp
  have base1' : c 1 0 = 2 := by rw [c0, c_zero, c_zero]; simp
  have base2 : c 2 1 = 8 := by rw [c1, base1, base1']; norm_num
  have base2' : c 2 0 = 4 := by
    rw [c0, base1', c3, c_zero, c_zero]; simp
  have base3 : c 3 1 = 24 := by rw [c1, base2, base2']; norm_num
  show c n 1 = _
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => omega
    | 1, _ => rw [base1]; simp [A131885]
    | 2, _ => rw [base2]; simp [A131885]
    | 3, _ => rw [base3]; simp [A131885]
    | (m + 4), ih =>
      rw [rec1, ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega),
        ih (m + 1) (by omega) (by omega)]
      show _ = (4 * A131885 (m + 3) - 6 * A131885 (m + 2) + 4 * A131885 (m + 1)) * _
      simp only [show m + 4 - 1 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega,
        show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega, pow_succ]
      ring

/-- The form quoted in the scan record, a(n) = A131885(n) * 2^n, fails at n = 1. -/
theorem scan_form_false : (A229136 1 : ℤ) ≠ A131885 1 * 2 ^ 1 := by
  rw [A229136_formula 1 le_rfl]; simp [A131885]
