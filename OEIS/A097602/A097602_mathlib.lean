/-
OEIS A097602 (offset 1): a(1) = 1, a(n+1) = a(n) + (number of squares among
a(1), ..., a(n)).  Conjecture (entry comment): a(n) = m^2 for some n iff
m mod 3 > 0.

Definitions.  `st i = (a(i+1), number of squares among a(1..i+1))`, built by
the recursion; `A097602 n = (st (n-1)).1`.  `A097602_succ` shows this is the
OEIS definition (the count is a `Finset` count over i = 1..n).

Main theorems.
* `A097602_succ`: a(n+1) = a(n) + #{1 <= i <= n : a(i) square} for n >= 1.
* `closed_form`: for every k the nine values a(9k+1), ..., a(9k+9) in closed
  form; in particular `A097602_9k1` a(9k+1) = (3k+1)^2 and `A097602_9k4`
  a(9k+4) = (3k+2)^2 (Jovovic's formulas in the entry).
* `A097602_isSquare_iff`: for n >= 1, a(n) is a square iff n mod 9 is 1 or 4.
* `A097602_conjecture`: (exists n >= 1, a(n) = m^2) iff m % 3 != 0, all m.

Proof.  Induction on k: after a(9k+1) = (3k+1)^2 the count is 2k+1; three
steps of 2k+1 reach (3k+2)^2 (count 2k+2); three steps of 2k+2 land on
(3k+3)^2 + 1, skipping (3k+3)^2; three more reach (3k+4)^2.  All other values
lie strictly between consecutive squares.

Not checked in this file: agreement with the OEIS b-file (certificate/check.py).
-/
import Mathlib

/-- `st i = (a(i+1), number of squares among a(1), ..., a(i+1))`. -/
def st : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => ((st n).1 + (st n).2,
              (st n).2 + if IsSquare ((st n).1 + (st n).2) then 1 else 0)

/-- OEIS A097602, offset 1. -/
def A097602 (n : ℕ) : ℕ := (st (n - 1)).1

lemma st_succ (n : ℕ) : st (n + 1) = ((st n).1 + (st n).2,
    (st n).2 + if IsSquare ((st n).1 + (st n).2) then 1 else 0) := rfl

lemma st_count (n : ℕ) :
    (st n).2 = ∑ i ∈ Finset.range (n + 1), if IsSquare (st i).1 then 1 else 0 := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    simp only [show IsSquare (st 0).1 from ⟨1, rfl⟩, ite_true]
    rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, st_succ]

theorem A097602_one : A097602 1 = 1 := rfl

theorem A097602_succ (n : ℕ) (hn : 1 ≤ n) :
    A097602 (n + 1) = A097602 n +
      ((Finset.Icc 1 n).filter (fun i => IsSquare (A097602 i))).card := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Finset.card_filter]
  have e : Finset.Icc 1 (j + 1) = Finset.Ico 1 (j + 2) := rfl
  rw [e, Finset.sum_Ico_eq_sum_range]
  simp only [A097602, Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega,
    Nat.add_sub_cancel_left]
  rw [← st_count, st_succ]

lemma not_sq {s v : ℕ} (h1 : s * s < v) (h2 : v < (s + 1) * (s + 1)) :
    ¬ IsSquare v := by
  rintro ⟨t, rfl⟩
  rcases le_or_gt t s with h | h
  · have := Nat.mul_le_mul h h; omega
  · have h' : s + 1 ≤ t := h
    have := Nat.mul_le_mul h' h'; omega

lemma step_ns {n v c v' : ℕ} (h : st n = (v, c)) (hv : v + c = v')
    (hns : ¬ IsSquare v') : st (n + 1) = (v', c) := by
  rw [st_succ, h]; simp only [hv, hns, ite_false, Nat.add_zero]

lemma step_sq {n v c v' : ℕ} (h : st n = (v, c)) (hv : v + c = v')
    (hs : IsSquare v') : st (n + 1) = (v', c + 1) := by
  rw [st_succ, h]; simp only [hv, hs, ite_true]

/-- The nine states of block k. -/
theorem closed_form (k : ℕ) :
    st (9 * k) = ((3 * k + 1) ^ 2, 2 * k + 1) ∧
    st (9 * k + 1) = ((3 * k + 1) ^ 2 + (2 * k + 1), 2 * k + 1) ∧
    st (9 * k + 2) = ((3 * k + 1) ^ 2 + 2 * (2 * k + 1), 2 * k + 1) ∧
    st (9 * k + 3) = ((3 * k + 2) ^ 2, 2 * k + 2) ∧
    st (9 * k + 4) = ((3 * k + 2) ^ 2 + (2 * k + 2), 2 * k + 2) ∧
    st (9 * k + 5) = ((3 * k + 2) ^ 2 + 2 * (2 * k + 2), 2 * k + 2) ∧
    st (9 * k + 6) = ((3 * k + 3) ^ 2 + 1, 2 * k + 2) ∧
    st (9 * k + 7) = ((3 * k + 3) ^ 2 + 1 + (2 * k + 2), 2 * k + 2) ∧
    st (9 * k + 8) = ((3 * k + 3) ^ 2 + 1 + 2 * (2 * k + 2), 2 * k + 2) := by
  have h0 : st (9 * k) = ((3 * k + 1) ^ 2, 2 * k + 1) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have h1 : st (9 * k + 1) = ((3 * k + 1) ^ 2 + (2 * k + 1), 2 * k + 1) :=
        step_ns ih rfl (not_sq (s := 3 * k + 1) (by nlinarith) (by nlinarith))
      have h2 : st (9 * k + 2) = ((3 * k + 1) ^ 2 + 2 * (2 * k + 1), 2 * k + 1) :=
        step_ns h1 (by ring) (not_sq (s := 3 * k + 1) (by nlinarith) (by nlinarith))
      have h3 : st (9 * k + 3) = ((3 * k + 2) ^ 2, 2 * k + 2) :=
        step_sq h2 (by ring) ⟨3 * k + 2, by ring⟩
      have h4 : st (9 * k + 4) = ((3 * k + 2) ^ 2 + (2 * k + 2), 2 * k + 2) :=
        step_ns h3 rfl (not_sq (s := 3 * k + 2) (by nlinarith) (by nlinarith))
      have h5 : st (9 * k + 5) = ((3 * k + 2) ^ 2 + 2 * (2 * k + 2), 2 * k + 2) :=
        step_ns h4 (by ring) (not_sq (s := 3 * k + 2) (by nlinarith) (by nlinarith))
      have h6 : st (9 * k + 6) = ((3 * k + 3) ^ 2 + 1, 2 * k + 2) :=
        step_ns h5 (by ring) (not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith))
      have h7 : st (9 * k + 7) = ((3 * k + 3) ^ 2 + 1 + (2 * k + 2), 2 * k + 2) :=
        step_ns h6 rfl (not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith))
      have h8 : st (9 * k + 8) = ((3 * k + 3) ^ 2 + 1 + 2 * (2 * k + 2), 2 * k + 2) :=
        step_ns h7 (by ring) (not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith))
      have h9 : st (9 * k + 8 + 1) = ((3 * (k + 1) + 1) ^ 2, 2 * k + 2 + 1) :=
        step_sq h8 (by ring) ⟨3 * (k + 1) + 1, by ring⟩
      rw [show 9 * (k + 1) = 9 * k + 8 + 1 by ring, h9]
      ext <;> ring
  have h1 : st (9 * k + 1) = ((3 * k + 1) ^ 2 + (2 * k + 1), 2 * k + 1) :=
    step_ns h0 rfl (not_sq (s := 3 * k + 1) (by nlinarith) (by nlinarith))
  have h2 : st (9 * k + 2) = ((3 * k + 1) ^ 2 + 2 * (2 * k + 1), 2 * k + 1) :=
    step_ns h1 (by ring) (not_sq (s := 3 * k + 1) (by nlinarith) (by nlinarith))
  have h3 : st (9 * k + 3) = ((3 * k + 2) ^ 2, 2 * k + 2) :=
    step_sq h2 (by ring) ⟨3 * k + 2, by ring⟩
  have h4 : st (9 * k + 4) = ((3 * k + 2) ^ 2 + (2 * k + 2), 2 * k + 2) :=
    step_ns h3 rfl (not_sq (s := 3 * k + 2) (by nlinarith) (by nlinarith))
  have h5 : st (9 * k + 5) = ((3 * k + 2) ^ 2 + 2 * (2 * k + 2), 2 * k + 2) :=
    step_ns h4 (by ring) (not_sq (s := 3 * k + 2) (by nlinarith) (by nlinarith))
  have h6 : st (9 * k + 6) = ((3 * k + 3) ^ 2 + 1, 2 * k + 2) :=
    step_ns h5 (by ring) (not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith))
  have h7 : st (9 * k + 7) = ((3 * k + 3) ^ 2 + 1 + (2 * k + 2), 2 * k + 2) :=
    step_ns h6 rfl (not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith))
  have h8 : st (9 * k + 8) = ((3 * k + 3) ^ 2 + 1 + 2 * (2 * k + 2), 2 * k + 2) :=
    step_ns h7 (by ring) (not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith))
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem A097602_9k1 (k : ℕ) : A097602 (9 * k + 1) = (3 * k + 1) ^ 2 := by
  simp [A097602, (closed_form k).1]

theorem A097602_9k4 (k : ℕ) : A097602 (9 * k + 4) = (3 * k + 2) ^ 2 := by
  simp [A097602, (closed_form k).2.2.2.1]

/-- Every value of block k other than the two squares is a non-square, and the
two squares are (3k+1)^2 and (3k+2)^2. -/
lemma block_values (k r : ℕ) (hr : r < 9) :
    (r = 0 ∧ (st (9 * k + r)).1 = (3 * k + 1) ^ 2) ∨
    (r = 3 ∧ (st (9 * k + r)).1 = (3 * k + 2) ^ 2) ∨
    (r ≠ 0 ∧ r ≠ 3 ∧ ¬ IsSquare (st (9 * k + r)).1) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := closed_form k
  interval_cases r
  · left; exact ⟨rfl, by simp [h0]⟩
  · right; right; refine ⟨by omega, by omega, ?_⟩; rw [h1]
    exact not_sq (s := 3 * k + 1) (by nlinarith) (by nlinarith)
  · right; right; refine ⟨by omega, by omega, ?_⟩; rw [h2]
    exact not_sq (s := 3 * k + 1) (by nlinarith) (by nlinarith)
  · right; left; exact ⟨rfl, by rw [h3]⟩
  · right; right; refine ⟨by omega, by omega, ?_⟩; rw [h4]
    exact not_sq (s := 3 * k + 2) (by nlinarith) (by nlinarith)
  · right; right; refine ⟨by omega, by omega, ?_⟩; rw [h5]
    exact not_sq (s := 3 * k + 2) (by nlinarith) (by nlinarith)
  · right; right; refine ⟨by omega, by omega, ?_⟩; rw [h6]
    exact not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith)
  · right; right; refine ⟨by omega, by omega, ?_⟩; rw [h7]
    exact not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith)
  · right; right; refine ⟨by omega, by omega, ?_⟩; rw [h8]
    exact not_sq (s := 3 * k + 3) (by nlinarith) (by nlinarith)

theorem A097602_isSquare_iff (n : ℕ) (hn : 1 ≤ n) :
    IsSquare (A097602 n) ↔ (n % 9 = 1 ∨ n % 9 = 4) := by
  have e : n - 1 = 9 * ((n - 1) / 9) + (n - 1) % 9 := (Nat.div_add_mod _ _).symm
  have hr : (n - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
  unfold A097602
  rw [e]
  rcases block_values ((n - 1) / 9) ((n - 1) % 9) hr with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h1, h2, hv⟩
  · rw [hv]; exact iff_of_true ⟨_, sq _⟩ (by omega)
  · rw [hv]; exact iff_of_true ⟨_, sq _⟩ (by omega)
  · exact iff_of_false hv (by omega)

theorem A097602_conjecture (m : ℕ) :
    (∃ n, 1 ≤ n ∧ A097602 n = m ^ 2) ↔ m % 3 ≠ 0 := by
  constructor
  · rintro ⟨n, hn, h⟩
    unfold A097602 at h
    have e : n - 1 = 9 * ((n - 1) / 9) + (n - 1) % 9 := (Nat.div_add_mod _ _).symm
    have hr : (n - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
    rw [e] at h
    rcases block_values ((n - 1) / 9) ((n - 1) % 9) hr with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, _, hv⟩
    · rw [hv] at h
      have := Nat.pow_left_injective (n := 2) (by norm_num) h
      omega
    · rw [hv] at h
      have := Nat.pow_left_injective (n := 2) (by norm_num) h
      omega
    · exact absurd ⟨m, by rw [h, sq]⟩ hv
  · intro h
    have e : m = 3 * (m / 3) + m % 3 := (Nat.div_add_mod _ _).symm
    rcases (show m % 3 = 1 ∨ m % 3 = 2 by omega) with h1 | h1
    · refine ⟨9 * (m / 3) + 1, by omega, ?_⟩
      rw [A097602_9k1]; conv_rhs => rw [e, h1]
    · refine ⟨9 * (m / 3) + 4, by omega, ?_⟩
      rw [A097602_9k4]; conv_rhs => rw [e, h1]
