import Mathlib
import OpenProblemsLib.Digits10

/-!
# OEIS A084043, A084044: a palindromic multiple of n containing n exists iff 10 does not divide n

A084043(n): smallest palindromic multiple of `n` in which the digit string of `n` appears with at least one
digit on each side, or 0 if none exists. A084044(n): smallest palindromic multiple of `n` containing the digit
string of `n` anywhere, or 0. Conjecture in both entries: `a(n) = 0` iff `10 ∣ n`.

Digit lists are Mathlib's `Nat.digits 10` (least significant digit first); reversing both strings preserves
"is a substring" and "is a palindrome", so the statements are those of the entries.

Checked here (for `n ≥ 1`):
* `A084043_main` : a positive palindromic multiple `P` of `n` with `digits n` strictly inside `digits P`
  (nonempty lists on both sides) exists iff `¬ 10 ∣ n`.
* `A084044_main` : the same with `digits n` an infix of `digits P`.
Construction: `n = g m` with `g = 2^a 5^b`, `gcd(m, 10) = 1`; `Y = Gp ++ D ++ rev D ++ rev Gp` where `D`
are the digits of `n` and `Gp` the digits of `g` padded to `e = a + b + 1` places; `P` = `k = 2 φ(m(10^|Y| - 1))`
copies of `Y`, so `g ∣ P` (low digits) and `m ∣ (10^{|Y| k} - 1)/(10^{|Y|} - 1)` (Euler).
-/

namespace A084043

open Nat OpenProblemsLib.Digits10

def IsPal (P : ℕ) : Prop := (Nat.digits 10 P).reverse = Nat.digits 10 P

def Sandwich (n P : ℕ) : Prop :=
  ∃ u v : List ℕ, u ≠ [] ∧ v ≠ [] ∧ Nat.digits 10 P = u ++ Nat.digits 10 n ++ v

theorem pal_head_eq_last (l : List ℕ) (hl : l ≠ []) (h : l.reverse = l) :
    l.head hl = l.getLast hl := by
  have := List.head_reverse (l := l) (by simpa using hl)
  simp only [h] at this
  exact this

/-- No palindromic positive multiple of a multiple of 10. -/
theorem no_pal_of_ten (P : ℕ) (hP : 0 < P) (h10 : 10 ∣ P) : ¬ IsPal P := by
  intro hpal
  have hne : Nat.digits 10 P ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hl := Nat.getLast_digit_ne_zero 10 (by omega : P ≠ 0)
  rw [← pal_head_eq_last _ hne hpal] at hl
  apply hl
  rw [List.head_eq_iff_head?_eq_some, Nat.digits_def' (by norm_num) hP]
  simp [Nat.mod_eq_zero_of_dvd h10]

theorem construct (n : ℕ) (hn : 0 < n) (h10 : ¬ 10 ∣ n) :
    ∃ P, 0 < P ∧ n ∣ P ∧ IsPal P ∧ Sandwich n P := by
  obtain ⟨a, n1, h2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 2 (by norm_num)
  have hn1 : n1 ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨b, m, h5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn1 5 (by norm_num)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn1)
  have h2m : ¬ 2 ∣ m := fun h => h2 (Dvd.dvd.mul_left h _)
  have hc : Nat.Coprime 10 m := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num]
    exact Nat.coprime_mul_iff_left.2 ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2m,
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5⟩
  set g := 2 ^ a * 5 ^ b with hg
  have hnm : 2 ^ a * (5 ^ b * m) = g * m := by rw [hg]; ring
  rw [hnm] at h10 hn ⊢
  set e := a + b + 1
  have hge : g ∣ 10 ^ e := by
    rw [show (10 : ℕ) ^ e = 2 ^ e * 5 ^ e by rw [← mul_pow]; norm_num]
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) (Nat.pow_dvd_pow 5 (by omega))
  have hglt : g < 10 ^ e := by
    have : g ≤ 10 ^ (a + b) := by
      rw [hg, pow_add]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) a) (Nat.pow_le_pow_left (by norm_num) b)
    have : 10 ^ (a + b) < 10 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hg0 : 0 < g := by positivity
  have hg10 : g % 10 ≠ 0 := fun h =>
    h10 (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h) (Dvd.intro m rfl))
  set G := Nat.digits 10 g
  have hGl : G.length ≤ e := (Nat.digits_length_le_iff (by norm_num) g).2 hglt
  set Gp := G ++ List.replicate (e - G.length) 0
  have hGp : Nat.ofDigits 10 Gp = g := by
    rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have hGpl : Gp.length = e := by simp [Gp]; omega
  have hGcons : G = g % 10 :: Nat.digits 10 (g / 10) := Nat.digits_def' (by norm_num) hg0
  set D := Nat.digits 10 (g * m)
  have hDne : D ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  set R := D ++ D.reverse ++ Gp.reverse
  set Y := Gp ++ R
  have hYpal : Y.reverse = Y := by simp [Y, R, List.append_assoc]
  have hYlast : ∃ X, Y = X ++ [g % 10] := by
    refine ⟨Gp ++ D ++ D.reverse ++ List.replicate (e - G.length) 0 ++ (Nat.digits 10 (g / 10)).reverse, ?_⟩
    simp only [Y, R, Gp, List.reverse_append, List.reverse_replicate, List.append_assoc, hGcons,
      List.reverse_cons]
  have hYlen : 1 ≤ Y.length := by simp [Y]; omega
  obtain ⟨j, hj⟩ := dvd_rep m Y.length hm0 hYlen hc
  set W := rp Y (j + 2)
  have hYmem : ∀ x ∈ Y, x ∈ G ∨ x ∈ D ∨ x = 0 := by
    intro x hx
    simp only [Y, R, Gp, List.mem_append, List.mem_reverse, List.mem_replicate] at hx
    tauto
  have hWlt : ∀ x ∈ W, x < 10 := by
    intro x hx
    rcases hYmem x (mem_rp hx) with hx | hx | rfl
    · exact Nat.digits_lt_base (by norm_num) hx
    · exact Nat.digits_lt_base (by norm_num) hx
    · norm_num
  have hWsplit : W = (rp Y (j + 1) ++ hYlast.choose) ++ [g % 10] := by
    rw [List.append_assoc, ← hYlast.choose_spec]
    exact (rp_comm Y (j + 1)).symm
  have hWlast : ∀ h : W ≠ [], W.getLast h ≠ 0 := by
    intro h
    simp only [hWsplit, List.getLast_append_singleton]
    exact hg10
  have hYne : Y ≠ [] := List.ne_nil_of_length_pos hYlen
  have hWne : W ≠ [] := by simp [W, rp, hYne]
  have hdig : Nat.digits 10 (Nat.ofDigits 10 W) = W := Nat.digits_ofDigits 10 (by norm_num) W hWlt hWlast
  refine ⟨Nat.ofDigits 10 W, ?_, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 W) with h | h
    · rw [h, Nat.digits_zero] at hdig; exact absurd hdig.symm hWne
    · exact h
  · rw [ofDigits_rp]
    apply Nat.mul_dvd_mul _ hj
    rw [Nat.ofDigits_append, hGp, hGpl]
    exact dvd_add dvd_rfl (Dvd.dvd.mul_right hge _)
  · rw [IsPal, hdig, rp_reverse, hYpal]
  · refine ⟨Y ++ Gp, D.reverse ++ Gp.reverse ++ rp Y j, by simp [hYne], by simp [hDne], ?_⟩
    rw [hdig]
    show Y ++ (Y ++ rp Y j) = Y ++ Gp ++ D ++ (D.reverse ++ Gp.reverse ++ rp Y j)
    simp only [Y, R, List.append_assoc]

theorem A084043_main (n : ℕ) (hn : 0 < n) :
    (∃ P, 0 < P ∧ n ∣ P ∧ IsPal P ∧ Sandwich n P) ↔ ¬ 10 ∣ n := by
  constructor
  · rintro ⟨P, hP, hnP, hpal, _⟩ h10
    exact no_pal_of_ten P hP (Nat.dvd_trans h10 hnP) hpal
  · exact construct n hn

theorem A084044_main (n : ℕ) (hn : 0 < n) :
    (∃ P, 0 < P ∧ n ∣ P ∧ IsPal P ∧ Nat.digits 10 n <:+: Nat.digits 10 P) ↔ ¬ 10 ∣ n := by
  constructor
  · rintro ⟨P, hP, hnP, hpal, _⟩ h10
    exact no_pal_of_ten P hP (Nat.dvd_trans h10 hnP) hpal
  · intro h
    obtain ⟨P, hP, hnP, hpal, u, v, _, _, huv⟩ := construct n hn h
    exact ⟨P, hP, hnP, hpal, u, v, huv.symm⟩
