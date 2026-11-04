/-
OEIS A080674, Mathlib proof.

A080674(n) = (4/3)(4^n - 1). Conjecture (A. Wajnberg, 2005): a(n) is the
number of integers from 0 to 10^n - 1 that lack 0, 1, 2, 3, 4 and 5 as a
digit.

Main theorem `A080674_main`: for every n, the number of x < 10^n whose
decimal digits (`A080674_decDigits x`: Mathlib's `Nat.digits 10 x`, and the
single digit 0 for x = 0, as 0 is written "0") all lie in {6, 7, 8, 9} is
4·(4^n - 1)/3 (an exact division). This is the README result; the
positional-notation step is proved here from Mathlib's `Nat.digits`
(`Nat.digits_def'`). Nothing is outside Lean.
-/
import Mathlib

/-- Decimal digits as written: 0 is written "0". -/
def A080674_decDigits (x : ℕ) : List ℕ := if x = 0 then [0] else Nat.digits 10 x

theorem A080674_decDigits_of_ne {x : ℕ} (hx : x ≠ 0) : A080674_decDigits x = Nat.digits 10 x := by
  simp [A080674_decDigits, hx]

/-- All Mathlib digits of x lie in D (true for x = 0, which has no digits). -/
def A080674_good (D : Finset ℕ) (x : ℕ) : Prop := ∀ d ∈ Nat.digits 10 x, d ∈ D

instance A080674_good_dec (D : Finset ℕ) : DecidablePred (A080674_good D) :=
  fun x => inferInstanceAs (Decidable (∀ d ∈ Nat.digits 10 x, d ∈ D))

/-- Count of x < 10^n all of whose Mathlib digits lie in D (x = 0 counts). -/
def A080674_G (D : Finset ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ n)).filter (A080674_good D)).card

theorem A080674_good_iff (D : Finset ℕ) (x : ℕ) (hx : x ≠ 0) :
    A080674_good D x ↔ x % 10 ∈ D ∧ A080674_good D (x / 10) := by
  unfold A080674_good
  rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hx)]
  simp

theorem A080674_card_split (P : ℕ → Prop) [DecidablePred P] (Q : ℕ → Prop) [DecidablePred Q]
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

theorem A080674_G_succ (D : Finset ℕ) (hD : D ⊆ Finset.range 10) (h0 : 0 ∉ D) (n : ℕ) :
    A080674_G D (n + 1) = 1 + D.card * A080674_G D n := by
  have hs : (Finset.range (10 ^ (n + 1))).filter (A080674_good D) =
      insert 0 ((Finset.range (10 * 10 ^ n)).filter
        (fun x => x % 10 ∈ D ∧ A080674_good D (x / 10))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, pow_succ, Nat.mul_comm _ 10]
    by_cases hx : x = 0
    · subst hx
      simp only [true_or, iff_true]
      exact ⟨by positivity, by simp [A080674_good]⟩
    · rw [A080674_good_iff D x hx]; simp [hx]
  have hD' : (Finset.range 10).filter (· ∈ D) = D := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hD h), h⟩⟩
  have h0' : 0 ∉ (Finset.range (10 * 10 ^ n)).filter (fun x => x % 10 ∈ D ∧ A080674_good D (x / 10)) := by
    simp [h0]
  rw [A080674_G, hs, Finset.card_insert_of_notMem h0',
    A080674_card_split (· ∈ D) (A080674_good D), hD', ← A080674_G]
  ring

/-- The count with 0 written as "0": positive x < 10^n with all digits in D. -/
theorem A080674_count_eq (D : Finset ℕ) (h0 : 0 ∉ D) (n : ℕ) :
    ((Finset.range (10 ^ n)).filter (fun x => ∀ d ∈ A080674_decDigits x, d ∈ D)).card + 1 =
      A080674_G D n := by
  have hs : (Finset.range (10 ^ n)).filter (A080674_good D) =
      insert 0 ((Finset.range (10 ^ n)).filter (fun x => ∀ d ∈ A080674_decDigits x, d ∈ D)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    by_cases hx : x = 0
    · subst hx
      simp only [true_or, iff_true]
      exact ⟨by positivity, by simp [A080674_good]⟩
    · rw [A080674_decDigits_of_ne hx]; simp [hx, A080674_good]
  have h0' : 0 ∉ (Finset.range (10 ^ n)).filter (fun x => ∀ d ∈ A080674_decDigits x, d ∈ D) := by
    rw [Finset.mem_filter]
    intro h
    exact h0 (h.2 0 (by simp [A080674_decDigits]))
  rw [A080674_G, hs, Finset.card_insert_of_notMem h0']

theorem A080674_G_zero (D : Finset ℕ) : A080674_G D 0 = 1 := by
  simp [A080674_G, Finset.filter_singleton, A080674_good]

theorem A080674_main (n : ℕ) :
    ((Finset.range (10 ^ n)).filter
      (fun x => ∀ d ∈ A080674_decDigits x, d ∈ ({6, 7, 8, 9} : Finset ℕ))).card =
      4 * (4 ^ n - 1) / 3 := by
  set D : Finset ℕ := {6, 7, 8, 9}
  have hD : D ⊆ Finset.range 10 := by decide
  have h0 : 0 ∉ D := by decide
  have hc : D.card = 4 := by decide
  have key : ∀ n, 3 * A080674_G D n = 4 ^ (n + 1) - 1 := by
    intro n
    induction n with
    | zero => rw [A080674_G_zero]; norm_num
    | succ k ih =>
      rw [A080674_G_succ D hD h0, hc, pow_succ]
      have : 1 ≤ 4 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega
  have h1 := A080674_count_eq D h0 n
  have h2 := key n
  rw [pow_succ] at h2
  have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  omega
