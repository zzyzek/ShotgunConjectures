import Mathlib

/-!
# OEIS A083125: palindromes divisible by 81

A083125: a(1) = 1, then the least unused number m such that a(n)·m is a palindrome.
Conjecture: every number not divisible by 10 occurs.

Checked here (a structural lemma explaining the observed delay of multiples of 81):
* `A083125_mod81`: for any digit list l, ofDigits 10 l ≡ S + 9·W (mod 81), where S is the digit
  sum and W = Σ i·l_i.
* `A083125_pal81`: if P is a base-10 palindrome and 81 ∣ P then 81 ∣ (digit sum of P).
* `A083125_pal81_large`: such P (P ≠ 0) satisfies 10^8 ≤ P.
Consequence (immediate from the definition): a multiple of 81 can be a(n+1) only if
a(n)·a(n+1) ≥ 10^8.

Not checked here: the conjecture itself (open), and the sequence computations.
-/

/-- W(l) = Σ i · l_i. -/
def A083125W : List ℕ → ℕ
  | [] => 0
  | _ :: l => A083125W l + l.sum

theorem A083125_mod81 (l : List ℕ) :
    ((Nat.ofDigits 10 l : ℕ) : ℤ) ≡ (l.sum : ℤ) + 9 * (A083125W l : ℤ) [ZMOD 81] := by
  induction l with
  | nil => simp [A083125W, Nat.ofDigits]
  | cons d l ih =>
    rw [Int.modEq_iff_dvd] at ih ⊢
    simp only [Nat.ofDigits_cons, List.sum_cons, A083125W, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
    have : ((d : ℤ) + ((l.sum : ℤ) + (9 * ((A083125W l : ℤ) + (l.sum : ℤ))))) -
        ((d : ℤ) + 10 * ((Nat.ofDigits 10 l : ℕ) : ℤ)) =
        10 * (((l.sum : ℤ) + 9 * (A083125W l : ℤ)) - ((Nat.ofDigits 10 l : ℕ) : ℤ)) -
          81 * (A083125W l : ℤ) := by ring
    rw [show ((d : ℤ) + (l.sum : ℤ) + 9 * ((A083125W l : ℤ) + (l.sum : ℤ))) =
      ((d : ℤ) + ((l.sum : ℤ) + (9 * ((A083125W l : ℤ) + (l.sum : ℤ))))) by ring, this]
    exact dvd_sub (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

theorem A083125_W_append (l : List ℕ) (d : ℕ) :
    A083125W (l ++ [d]) = A083125W l + l.length * d := by
  induction l with
  | nil => simp [A083125W]
  | cons e l ih =>
    simp only [List.cons_append, A083125W, ih, List.sum_append, List.sum_cons, List.sum_nil,
      List.length_cons]
    ring

theorem A083125_W_reverse (l : List ℕ) :
    A083125W l + A083125W l.reverse + l.sum = l.length * l.sum := by
  induction l with
  | nil => simp [A083125W]
  | cons d l ih =>
    simp only [A083125W, List.reverse_cons, A083125_W_append, List.length_reverse,
      List.sum_cons, List.length_cons]
    nlinarith [ih]

theorem A083125_pal81 (P : ℕ) (hpal : (Nat.digits 10 P).reverse = Nat.digits 10 P)
    (h : 81 ∣ P) : 81 ∣ (Nat.digits 10 P).sum := by
  set l := Nat.digits 10 P with hl
  have hP : Nat.ofDigits 10 l = P := Nat.ofDigits_digits 10 P
  have hW := A083125_W_reverse l
  rw [hpal] at hW
  have hm := A083125_mod81 l
  rw [hP] at hm
  -- 2P ≡ S (9n - 7) (mod 81), n = length
  have key : (81 : ℤ) ∣ (l.sum : ℤ) * (9 * (l.length : ℤ) - 7) := by
    have h1 : (81 : ℤ) ∣ (P : ℤ) := by exact_mod_cast h
    have h2 : (81 : ℤ) ∣ (P : ℤ) - ((l.sum : ℤ) + 9 * (A083125W l : ℤ)) :=
      Int.ModEq.dvd hm.symm
    have hW' : (2 * (A083125W l : ℤ)) = (l.length : ℤ) * l.sum - l.sum := by
      have := congrArg (Nat.cast : ℕ → ℤ) hW
      simp only [Nat.cast_add, Nat.cast_mul] at this
      linarith
    have : (l.sum : ℤ) * (9 * (l.length : ℤ) - 7) =
        2 * (P : ℤ) - 2 * ((P : ℤ) - ((l.sum : ℤ) + 9 * (A083125W l : ℤ))) := by
      linear_combination (-9 : ℤ) * hW'
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  have hcop : IsCoprime (81 : ℤ) (9 * (l.length : ℤ) - 7) := by
    have h3 : IsCoprime (3 : ℤ) (9 * (l.length : ℤ) - 7) :=
      ⟨3 * (l.length : ℤ) - 2, -1, by ring⟩
    have : (81 : ℤ) = 3 ^ 4 := by norm_num
    rw [this]; exact h3.pow_left
  have := hcop.dvd_of_dvd_mul_right key
  exact_mod_cast this

theorem A083125_pal81_large (P : ℕ) (hP0 : P ≠ 0)
    (hpal : (Nat.digits 10 P).reverse = Nat.digits 10 P) (h : 81 ∣ P) : 10 ^ 8 ≤ P := by
  have hs := A083125_pal81 P hpal h
  have hsum_pos : 0 < (Nat.digits 10 P).sum := by
    rcases Nat.eq_zero_or_pos (Nat.digits 10 P).sum with h0 | h0
    · exfalso
      have : Nat.ofDigits 10 (Nat.digits 10 P) = 0 := by
        rw [Nat.ofDigits_eq_sum_mapIdx]
        apply List.sum_eq_zero
        intro x hx
        rw [List.mem_mapIdx] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have : (Nat.digits 10 P)[i] = 0 := by
          have hmem := List.getElem_mem hi
          have := List.le_sum_of_mem hmem
          omega
        simp [this]
      rw [Nat.ofDigits_digits] at this; exact hP0 this
    · exact h0
  have h81 : 81 ≤ (Nat.digits 10 P).sum := Nat.le_of_dvd hsum_pos hs
  have hle : (Nat.digits 10 P).sum ≤ (Nat.digits 10 P).length * 9 := by
    have := List.sum_le_length_nsmul (Nat.digits 10 P) 9
      (fun x hx => Nat.lt_succ_iff.1 (Nat.digits_lt_base (by norm_num) hx))
    simpa [mul_comm] using this
  have hlen : 9 ≤ (Nat.digits 10 P).length := by omega
  have hb := Nat.base_pow_length_digits_le 10 P (by norm_num) hP0
  have : 10 ^ 9 ≤ 10 * P :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hlen) hb
  omega
