import Mathlib

/-!
# OEIS A084029: every row of the triangle has a nonzero first entry

A084029: row `n` lists the first `n` `n`-digit multiples of `n` with digit sum `n`, padded with 0.
Conjecture: only one term is zero (row 2). This file proves the weaker statement that every row has at least
one nonzero entry: for every `n ≥ 1` there is an `n`-digit multiple of `n` with digit sum `n`.

Checked here:
* `digitSum_ofDigits` : a digit list with entries `< 10` has the same sum as the digits of its value.
* `ofDigits_ofFn` : `ofDigits b (ofFn f) = ∑ i, f i * b^i`.
* `A084029_row_nonempty` : for `n ≥ 1` there is `N` with `n` decimal digits, `n ∣ N` and digit sum `n`.
  Proof: Erdős–Ginzburg–Ziv (`Int.erdos_ginzburg_ziv`) applied to two copies of each `10^i`, `i < n`,
  gives `n` of them with sum divisible by `n`; their sum has digits in `{0, 1, 2}` and digit sum `n`; shift it
  left to exactly `n` digits.
Not checked: the conjecture itself (at least `n` such numbers for `n ≥ 3`).
-/

namespace A084029

open Nat Finset

theorem digitSum_ofDigits (L : List ℕ) (h : ∀ x ∈ L, x < 10) :
    (Nat.digits 10 (Nat.ofDigits 10 L)).sum = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.ofDigits_cons, List.sum_cons]
    by_cases h0 : a = 0 ∧ Nat.ofDigits 10 L = 0
    · obtain ⟨rfl, hL⟩ := h0
      rw [hL] at ih' ⊢
      simp at ih' ⊢
      omega
    · have hxy : a ≠ 0 ∨ Nat.ofDigits 10 L ≠ 0 := by tauto
      rw [Nat.digits_add 10 (by norm_num) a _ ha hxy, List.sum_cons, ih']

theorem ofDigits_ofFn (b : ℕ) : ∀ (n : ℕ) (f : Fin n → ℕ),
    Nat.ofDigits b (List.ofFn f) = ∑ i : Fin n, f i * b ^ (i : ℕ)
  | 0, f => by simp
  | n + 1, f => by
    rw [List.ofFn_succ, Nat.ofDigits_cons, ofDigits_ofFn b n, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem A084029_row_nonempty (n : ℕ) (hn : 1 ≤ n) :
    ∃ N, (Nat.digits 10 N).length = n ∧ n ∣ N ∧ (Nat.digits 10 N).sum = n := by
  classical
  obtain ⟨t, -, ht, hdiv⟩ := Int.erdos_ginzburg_ziv (n := n) (s := (univ : Finset (Fin n × Fin 2)))
    (fun x => (10 : ℤ) ^ (x.1 : ℕ)) (by simp; omega)
  set c : Fin n → ℕ := fun i => (t.filter (fun x => x.1 = i)).card with hc
  have hc2 : ∀ i, c i ≤ 2 := by
    intro i
    have hsub : t.filter (fun x => x.1 = i) ⊆ ({(i, 0), (i, 1)} : Finset (Fin n × Fin 2)) := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨x1, x2⟩ := x
      simp only at hx
      obtain ⟨-, rfl⟩ := hx
      fin_cases x2 <;> simp
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  set L := List.ofFn c with hL
  have hLlt : ∀ x ∈ L, x < 10 := by
    intro x hx
    rw [hL, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have := hc2 i
    omega
  have hLsum : L.sum = n := by
    rw [hL, List.sum_ofFn]
    calc ∑ i, c i = t.card := (Finset.card_eq_sum_card_fiberwise (s := t) (t := univ)
          (f := fun x : Fin n × Fin 2 => x.1) (fun _ _ => Finset.mem_univ _)).symm
      _ = n := ht
  set M := Nat.ofDigits 10 L with hM
  have hMval : (M : ℤ) = ∑ x ∈ t, (10 : ℤ) ^ (x.1 : ℕ) := by
    rw [hM, hL, ofDigits_ofFn]
    push_cast
    rw [← Finset.sum_fiberwise (s := t) (g := fun x => x.1) (f := fun x => (10 : ℤ) ^ (x.1 : ℕ))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_congr rfl (g := fun _ => (10 : ℤ) ^ (i : ℕ)) (by
      intro x hx; simp only [Finset.mem_filter] at hx; rw [hx.2])]
    simp [c]
  have hnM : n ∣ M := by
    have : (n : ℤ) ∣ (M : ℤ) := by rw [hMval]; exact hdiv
    exact Int.natCast_dvd_natCast.1 this
  have hMsum : (Nat.digits 10 M).sum = n := by rw [hM, digitSum_ofDigits L hLlt, hLsum]
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h] at hMsum; simp at hMsum; omega
    · exact h
  have hMlt : M < 10 ^ n := by
    have := Nat.ofDigits_lt_base_pow_length (b := 10) (by norm_num) hLlt
    rwa [hL, List.length_ofFn] at this
  have hlen : (Nat.digits 10 M).length ≤ n := (Nat.digits_length_le_iff (by norm_num) M).2 hMlt
  refine ⟨10 ^ (n - (Nat.digits 10 M).length) * M, ?_, Dvd.dvd.mul_left hnM _, ?_⟩
  · rw [Nat.digits_base_pow_mul (by norm_num) hM0, List.length_append, List.length_replicate]
    omega
  · rw [Nat.digits_base_pow_mul (by norm_num) hM0, List.sum_append, List.sum_replicate, hMsum]
    simp
