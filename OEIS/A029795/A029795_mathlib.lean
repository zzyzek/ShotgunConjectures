import Mathlib

/-
OEIS A029795 (Mathlib): numbers k such that k and k^3 have the same set of decimal digits.
Conjecture (C. R. Greathouse IV, 2011): there are m and N with a(n) = m + n for all n ≥ N.
README result: false.

Main theorem `A029795_main`: with `A029795_S k` meaning
`(Nat.digits 10 k).toFinset = (Nat.digits 10 (k ^ 3)).toFinset` and a = `Nat.nth A029795_S`
(the terms in increasing order, 0-indexed; any fixed index shift is absorbed by m), there are
no m : ℤ and N : ℕ with a(n) = m + n for all n ≥ N.

Proof. If a(n) = m + n for n ≥ N, the set of terms is infinite (a finite set would make
a(n) = 0 for large n), so every a(n) is a term and every integer x ≥ max(m + N, 0) is a term.
But x = 10^e + 1 (e ≥ 1) has no digit 3 while (10^e + 1)^3 has digit 3 at position e
(`no3`, `cube3`, restated from the core file A029795.lean); the positional digit
x / 10^j % 10 is linked to `Nat.digits` by `Nat.getD_digits`.

Outside Lean: nothing.
-/

def A029795_S (k : ℕ) : Prop := (Nat.digits 10 k).toFinset = (Nat.digits 10 (k ^ 3)).toFinset

theorem A029795_pow10_mod (e : Nat) (he : 1 ≤ e) : 10 ^ e % 10 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [Nat.pow_succ]; exact Nat.mul_mod_left _ _

theorem A029795_cube3 (e : Nat) (he : 1 ≤ e) : (10 ^ e + 1) ^ 3 / 10 ^ e % 10 = 3 := by
  have hP : 10 ≤ 10 ^ e := by
    have := Nat.pow_le_pow_right (show 10 > 0 by decide) he
    simpa using this
  have h0 := A029795_pow10_mod e he
  generalize 10 ^ e = P at hP h0
  have hc : (P + 1) ^ 3 = P * (P * P + 3 * P + 3) + 1 := by ring
  rw [hc, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have h1 : P * P % 10 = 0 := by rw [Nat.mul_mod, h0]
  omega

theorem A029795_no3 (e : Nat) (he : 1 ≤ e) (j : Nat) : (10 ^ e + 1) / 10 ^ j % 10 ≠ 3 := by
  by_cases hj0 : j = 0
  · subst hj0
    have := A029795_pow10_mod e he
    simp only [Nat.pow_zero, Nat.div_one]
    omega
  by_cases hje : j ≤ e
  · have hpos : 10 ≤ 10 ^ j := by
      have := Nat.pow_le_pow_right (show 10 > 0 by decide) (show 1 ≤ j by omega)
      simpa using this
    have hsplit : 10 ^ e = 10 ^ j * 10 ^ (e - j) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hsplit, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
    by_cases hej : e - j = 0
    · rw [hej]; decide
    · have := A029795_pow10_mod (e - j) (by omega)
      omega
  · have hlt : 10 ^ e + 1 < 10 ^ j := by
      have h1 : 10 ^ (e + 1) ≤ 10 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 10 ^ (e + 1) = 10 ^ e * 10 := by rw [Nat.pow_succ]
      have h3 : 1 ≤ 10 ^ e := Nat.pow_pos (by decide)
      omega
    rw [Nat.div_eq_of_lt hlt]; decide

/-- A nonzero digit d occurs in `Nat.digits 10 x` iff x / 10^j % 10 = d for some j. -/
theorem A029795_mem_digits (x d : ℕ) (hd : d ≠ 0) :
    d ∈ Nat.digits 10 x ↔ ∃ j, x / 10 ^ j % 10 = d := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    refine ⟨j, ?_⟩
    rw [← Nat.getD_digits x j (by norm_num), List.getD_eq_getElem _ _ hj]
  · rintro ⟨j, hj⟩
    have hlen : j < (Nat.digits 10 x).length := by
      by_contra hc
      have h1 := Nat.lt_base_pow_length_digits (b := 10) (m := x) (by norm_num)
      have h2 : 10 ^ (Nat.digits 10 x).length ≤ 10 ^ j :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.div_eq_of_lt (by omega)] at hj
      exact hd (by simpa using hj.symm)
    have := Nat.getD_digits x j (b := 10) (by norm_num)
    rw [List.getD_eq_getElem _ _ hlen, hj] at this
    rw [← this]
    exact List.getElem_mem hlen

/-- No bound M has every x ≥ M a term. -/
theorem A029795_not_cofinite (M : ℕ) : ∃ x, M ≤ x ∧ ¬ A029795_S x := by
  refine ⟨10 ^ (M + 1) + 1, ?_, ?_⟩
  · have : M + 1 < 10 ^ (M + 1) := Nat.lt_pow_self (by norm_num)
    omega
  · intro hS
    have h3 : 3 ∈ Nat.digits 10 ((10 ^ (M + 1) + 1) ^ 3) :=
      (A029795_mem_digits _ 3 (by norm_num)).mpr ⟨M + 1, A029795_cube3 (M + 1) (by omega)⟩
    have h3' : 3 ∈ Nat.digits 10 (10 ^ (M + 1) + 1) := by
      have : 3 ∈ (Nat.digits 10 ((10 ^ (M + 1) + 1) ^ 3)).toFinset := List.mem_toFinset.mpr h3
      rw [A029795_S] at hS
      rw [← hS] at this
      exact List.mem_toFinset.mp this
    obtain ⟨j, hj⟩ := (A029795_mem_digits _ 3 (by norm_num)).mp h3'
    exact A029795_no3 (M + 1) (by omega) j hj

theorem A029795_main :
    ¬ ∃ (m : ℤ) (N : ℕ), ∀ n, N ≤ n → (Nat.nth A029795_S n : ℤ) = m + n := by
  rintro ⟨m, N, h⟩
  -- The set of terms is infinite: otherwise a(n) = 0 for all large n.
  --
  have hinf : (Set.ofPred A029795_S).Infinite := by
    intro hf
    let c := max N hf.toFinset.card
    have e1 := Nat.nth_of_card_le hf (n := c) (le_max_right _ _)
    have e2 := Nat.nth_of_card_le hf (n := c + 1) (by omega)
    have h1 := h c (le_max_left _ _)
    have h2 := h (c + 1) (by omega)
    rw [e1] at h1
    rw [e2] at h2
    push_cast at h1 h2
    omega
  -- Every x ≥ max(m + N, 0) is a term.
  --
  obtain ⟨x, hx, hnot⟩ := A029795_not_cofinite ((m + N).toNat)
  apply hnot
  have hn : N ≤ ((x : ℤ) - m).toNat := by omega
  have hv := h _ hn
  have hx' : (((x : ℤ) - m).toNat : ℤ) = x - m := by omega
  rw [hx'] at hv
  have : Nat.nth A029795_S (((x : ℤ) - m).toNat) = x := by omega
  rw [← this]
  exact Nat.nth_mem_of_infinite hinf _
