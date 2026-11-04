/-
OEIS A104896, Mathlib proof.

A104896: a(0) = 0, a(n) = 7·a(n-1) + 7. Conjecture: a(n) is also the number
of integers from 0 to 10^n - 1 that lack 0, 1 and 2 as a digit.

Main theorem `A104896_main`: for every n, the number of x < 10^n whose
decimal digits (`A104896_decDigits x`: Mathlib's `Nat.digits 10 x`, and the
single digit 0 for x = 0, as 0 is written "0") all lie in {3, ..., 9}
equals `A104896 n` (the recurrence). This is the README result; the
positional-notation step is proved here from Mathlib's `Nat.digits`
(`Nat.digits_def'`). Nothing is outside Lean.
-/
import Mathlib

/-- A104896: a(0) = 0, a(n+1) = 7 a(n) + 7. -/
def A104896 : ℕ → ℕ
  | 0 => 0
  | n + 1 => 7 * A104896 n + 7

/-- Decimal digits as written: 0 is written "0". -/
def A104896_decDigits (x : ℕ) : List ℕ := if x = 0 then [0] else Nat.digits 10 x

theorem A104896_decDigits_of_ne {x : ℕ} (hx : x ≠ 0) : A104896_decDigits x = Nat.digits 10 x := by
  simp [A104896_decDigits, hx]

/-- All Mathlib digits of x lie in D (true for x = 0, which has no digits). -/
def A104896_good (D : Finset ℕ) (x : ℕ) : Prop := ∀ d ∈ Nat.digits 10 x, d ∈ D

instance A104896_good_dec (D : Finset ℕ) : DecidablePred (A104896_good D) :=
  fun x => inferInstanceAs (Decidable (∀ d ∈ Nat.digits 10 x, d ∈ D))

/-- Count of x < 10^n all of whose Mathlib digits lie in D (x = 0 counts). -/
def A104896_G (D : Finset ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ n)).filter (A104896_good D)).card

theorem A104896_good_iff (D : Finset ℕ) (x : ℕ) (hx : x ≠ 0) :
    A104896_good D x ↔ x % 10 ∈ D ∧ A104896_good D (x / 10) := by
  unfold A104896_good
  rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hx)]
  simp

theorem A104896_card_split (P : ℕ → Prop) [DecidablePred P] (Q : ℕ → Prop) [DecidablePred Q]
    (m : ℕ) :
    ((Finset.range (10 * m)).filter (fun x => P (x % 10) ∧ Q (x / 10))).card =
      ((Finset.range 10).filter P).card * ((Finset.range m).filter Q).card := by
  rw [← Finset.card_product]
  symm
  apply Finset.card_bij (fun p _ => p.1 + 10 * p.2)
  · rintro ⟨r, q⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at h ⊢
    refine ⟨by omega, ?_, ?_⟩
    · rw [show (r + 10 * q) % 10 = r by omega]; exact h.1.2
    · rw [show (r + 10 * q) / 10 = q by omega]; exact h.2.2
  · rintro ⟨r, q⟩ h ⟨r', q'⟩ h' he
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at h h'
    simp only at he
    have : r = r' := by omega
    have : q = q' := by omega
    simp_all
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    refine ⟨(x % 10, x / 10), ?_, by simp only; omega⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, hx.2.1⟩, ⟨by omega, hx.2.2⟩⟩

theorem A104896_G_succ (D : Finset ℕ) (hD : D ⊆ Finset.range 10) (h0 : 0 ∉ D) (n : ℕ) :
    A104896_G D (n + 1) = 1 + D.card * A104896_G D n := by
  have hs : (Finset.range (10 ^ (n + 1))).filter (A104896_good D) =
      insert 0 ((Finset.range (10 * 10 ^ n)).filter
        (fun x => x % 10 ∈ D ∧ A104896_good D (x / 10))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, pow_succ, Nat.mul_comm _ 10]
    by_cases hx : x = 0
    · subst hx
      simp only [true_or, iff_true]
      exact ⟨by positivity, by simp [A104896_good]⟩
    · rw [A104896_good_iff D x hx]; simp [hx]
  have hD' : (Finset.range 10).filter (· ∈ D) = D := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hD h), h⟩⟩
  have h0' : 0 ∉ (Finset.range (10 * 10 ^ n)).filter (fun x => x % 10 ∈ D ∧ A104896_good D (x / 10)) := by
    simp [h0]
  rw [A104896_G, hs, Finset.card_insert_of_notMem h0',
    A104896_card_split (· ∈ D) (A104896_good D), hD', ← A104896_G]
  ring

/-- The count with 0 written as "0": positive x < 10^n with all digits in D. -/
theorem A104896_count_eq (D : Finset ℕ) (h0 : 0 ∉ D) (n : ℕ) :
    ((Finset.range (10 ^ n)).filter (fun x => ∀ d ∈ A104896_decDigits x, d ∈ D)).card + 1 =
      A104896_G D n := by
  have hs : (Finset.range (10 ^ n)).filter (A104896_good D) =
      insert 0 ((Finset.range (10 ^ n)).filter (fun x => ∀ d ∈ A104896_decDigits x, d ∈ D)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    by_cases hx : x = 0
    · subst hx
      simp only [true_or, iff_true]
      exact ⟨by positivity, by simp [A104896_good]⟩
    · rw [A104896_decDigits_of_ne hx]; simp [hx, A104896_good]
  have h0' : 0 ∉ (Finset.range (10 ^ n)).filter (fun x => ∀ d ∈ A104896_decDigits x, d ∈ D) := by
    rw [Finset.mem_filter]
    intro h
    exact h0 (h.2 0 (by simp [A104896_decDigits]))
  rw [A104896_G, hs, Finset.card_insert_of_notMem h0']

theorem A104896_G_zero (D : Finset ℕ) : A104896_G D 0 = 1 := by
  simp [A104896_G, Finset.filter_singleton, A104896_good]

theorem A104896_main (n : ℕ) :
    ((Finset.range (10 ^ n)).filter
      (fun x => ∀ d ∈ A104896_decDigits x, d ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ))).card =
      A104896 n := by
  set D : Finset ℕ := {3, 4, 5, 6, 7, 8, 9}
  have hD : D ⊆ Finset.range 10 := by decide
  have h0 : 0 ∉ D := by decide
  have hc : D.card = 7 := by decide
  have key : ∀ n, A104896_G D n = A104896 n + 1 := by
    intro n
    induction n with
    | zero => rw [A104896_G_zero]; rfl
    | succ k ih =>
      rw [A104896_G_succ D hD h0, hc, ih, A104896]
      ring
  have h1 := A104896_count_eq D h0 n
  rw [key n] at h1
  omega
