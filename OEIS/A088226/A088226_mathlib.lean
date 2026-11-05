/-
OEIS A088226, Mathlib proof of R. Stephan's conjecture with the index shift it needs.

a(1) = 0, a(2) = 0, a(3) = 1, a(n) = |a(n-1) - a(n-2) - a(n-3)| for n > 3 (`A088226_a`;
a(0) is not part of the sequence and is set to 0).
f(m) = m'/2 where m' is the smallest even number of the form |m - s^2|, s ∈ ℕ (`A088226_f`).

Main theorem `A088226_main`: a(n) = f(n - 1) for every n ≥ 1.
`A088226_literal_fails`: a(2) = 0 but f(2) = 1, so the conjecture as printed ("a(n) = m/2
where m is the smallest even distance from n to a square") is false at n = 2.
`A088226_data`: the 105 printed terms.

Proof. Block lemma `A088226_block`: for k ≥ 0 and 1 ≤ j ≤ 2k + 1,
a(k^2 + j) = (j - 1)/2 for odd j and k - (j - 2)/2 for even j (induction on k, inside a
block on j; the first three entries of a block use the last three of the previous one).
`A088226_f_block`: f(k^2 + j - 1) is the same value, because k^2 and (k+1)^2 are at
distances j - 1 and 2k + 2 - j (one odd, one even) and every other square is farther.

Not checked: nothing (the statement is checked for all n).
-/
import Mathlib

/-- A088226: a(1) = 0, a(2) = 0, a(3) = 1, a(n) = |a(n-1) - a(n-2) - a(n-3)|. -/
def A088226_a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | n + 4 => Int.natAbs ((A088226_a (n + 3) : ℤ) - A088226_a (n + 2) - A088226_a (n + 1))

theorem A088226_data :
    (List.range 105).map (fun i => A088226_a (i + 1)) =
      [0,0,1,1,0,2,1,1,2,0,3,1,2,2,1,3,0,4,1,3,2,2,3,1,4,0,5,1,4,2,3,3,2,4,
       1,5,0,6,1,5,2,4,3,3,4,2,5,1,6,0,7,1,6,2,5,3,4,4,3,5,2,6,1,7,0,8,1,7,
       2,6,3,5,4,4,5,3,6,2,7,1,8,0,9,1,8,2,7,3,6,4,5,5,4,6,3,7,2,8,1,9,0,10,1,9,2] := by
  decide

/-- Some even number is a distance |m - s^2| (s = m gives m^2 - m). -/
theorem A088226_exists (m : ℕ) : ∃ d, Even d ∧ ∃ s : ℕ, Int.natAbs ((m : ℤ) - (s : ℤ) ^ 2) = d :=
  ⟨Int.natAbs ((m : ℤ) - (m : ℤ) ^ 2), by
    rw [Int.natAbs_even, show (m : ℤ) - (m : ℤ) ^ 2 = -((m : ℤ) * (m - 1)) by ring, even_neg]
    exact Int.even_mul_pred_self _, m, rfl⟩

open Classical in
/-- Half the smallest even distance from m to a square. -/
noncomputable def A088226_f (m : ℕ) : ℕ := Nat.find (A088226_exists m) / 2

/-- The block value: (j - 1)/2 for odd j, k - (j - 2)/2 for even j. -/
def A088226_G (k j : ℕ) : ℕ := if j % 2 = 1 then (j - 1) / 2 else k - (j - 2) / 2

theorem A088226_rec (n : ℕ) :
    A088226_a (n + 4) =
      Int.natAbs ((A088226_a (n + 3) : ℤ) - A088226_a (n + 2) - A088226_a (n + 1)) := by
  rw [A088226_a]

theorem A088226_G_odd {k j : ℕ} (h : j % 2 = 1) : A088226_G k j = (j - 1) / 2 := by
  simp [A088226_G, h]

theorem A088226_G_even {k j : ℕ} (h : j % 2 = 0) : A088226_G k j = k - (j - 2) / 2 := by
  simp [A088226_G, h]

theorem A088226_block (k : ℕ) :
    ∀ n, k ^ 2 + 1 ≤ n → n ≤ k ^ 2 + 2 * k + 1 → A088226_a n = A088226_G k (n - k ^ 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    match k, ihk with
    | 0, _ =>
      intro n h1 h2
      obtain rfl : n = 1 := by omega
      decide
    | 1, _ =>
      intro n h1 h2
      obtain rfl | rfl | rfl : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      all_goals decide
    | k + 2, ihk =>
      have ih := ihk (k + 1) (by omega)
      have hq : (k + 2) ^ 2 = (k + 1) ^ 2 + 2 * k + 3 := by ring
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ihn =>
        intro h1 h2
        rw [hq] at h1 h2 ihn ⊢
        generalize hK : (k + 1) ^ 2 = K at *
        obtain ⟨j, rfl⟩ : ∃ j, n = K + 2 * k + 3 + j := ⟨n - (K + 2 * k + 3), by omega⟩
        obtain ⟨m, hm⟩ : ∃ m, K + 2 * k + 3 + j = m + 4 := ⟨K + 2 * k + 3 + j - 4, by omega⟩
        rw [hm, A088226_rec, ← hm]
        rw [show K + 2 * k + 3 + j - (K + 2 * k + 3) = j by omega]
        -- Values in block k + 1 (index K + i) and in block k + 2 (index K + 2k + 3 + i).
        --
        have v1 : ∀ i, 1 ≤ i → i ≤ 2 * k + 3 → A088226_a (K + i) = A088226_G (k + 1) i := by
          intro i hi1 hi2
          rw [ih (K + i) (by omega) (by omega)]
          congr 1
          omega
        have v2 : ∀ i, 1 ≤ i → i < j → A088226_a (K + 2 * k + 3 + i) = A088226_G (k + 2) i := by
          intro i hi1 hi2
          rw [ihn (K + 2 * k + 3 + i) (by omega) (by omega) (by omega)]
          congr 1
          omega
        rcases Nat.lt_or_ge j 4 with hj | hj
        · obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
          · rw [show m + 3 = K + (2 * k + 3) by omega, show m + 2 = K + (2 * k + 2) by omega,
              show m + 1 = K + (2 * k + 1) by omega, v1 _ (by omega) le_rfl,
              v1 _ (by omega) (by omega), v1 _ (by omega) (by omega),
              A088226_G_odd (by omega), A088226_G_even (by omega), A088226_G_odd (by omega),
              A088226_G_odd (by omega)]
            omega
          · rw [show m + 3 = K + 2 * k + 3 + 1 by omega, show m + 2 = K + (2 * k + 3) by omega,
              show m + 1 = K + (2 * k + 2) by omega, v2 1 le_rfl (by omega),
              v1 _ (by omega) le_rfl, v1 _ (by omega) (by omega),
              A088226_G_odd (by omega), A088226_G_odd (by omega), A088226_G_even (by omega),
              A088226_G_even (by omega)]
            omega
          · rw [show m + 3 = K + 2 * k + 3 + 2 by omega, show m + 2 = K + 2 * k + 3 + 1 by omega,
              show m + 1 = K + (2 * k + 3) by omega, v2 2 (by omega) (by omega),
              v2 1 le_rfl (by omega), v1 _ (by omega) le_rfl,
              A088226_G_even (by omega), A088226_G_odd (by omega), A088226_G_odd (by omega),
              A088226_G_odd (by omega)]
            omega
        · rw [show m + 3 = K + 2 * k + 3 + (j - 1) by omega,
            show m + 2 = K + 2 * k + 3 + (j - 2) by omega,
            show m + 1 = K + 2 * k + 3 + (j - 3) by omega,
            v2 _ (by omega) (by omega), v2 _ (by omega) (by omega), v2 _ (by omega) (by omega)]
          rcases Nat.mod_two_eq_zero_or_one j with hp | hp
          · rw [A088226_G_odd (by omega), A088226_G_even (by omega), A088226_G_odd (by omega),
              A088226_G_even hp]
            omega
          · rw [A088226_G_even (by omega), A088226_G_odd (by omega), A088226_G_even (by omega),
              A088226_G_odd hp]
            omega

theorem A088226_f_block (k j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2 * k + 1) :
    A088226_f (k ^ 2 + j - 1) = A088226_G k j := by
  classical
  obtain ⟨K, hK⟩ : ∃ K, k ^ 2 = K := ⟨_, rfl⟩
  have hK1 : (k + 1) ^ 2 = K + 2 * k + 1 := by rw [← hK]; ring
  rw [hK]
  -- The smallest even distance is c = 2 G(k, j).
  --
  have key : Nat.find (A088226_exists (K + j - 1)) = 2 * A088226_G k j := by
    rw [Nat.find_eq_iff]
    constructor
    · refine ⟨⟨A088226_G k j, by ring⟩, ?_⟩
      rcases Nat.mod_two_eq_zero_or_one j with hp | hp
      · rw [A088226_G_even hp]
        refine ⟨k + 1, ?_⟩
        rw [show ((k + 1 : ℕ) : ℤ) ^ 2 = ((K + 2 * k + 1 : ℕ) : ℤ) by rw [← hK1]; push_cast; ring]
        omega
      · rw [A088226_G_odd hp]
        refine ⟨k, ?_⟩
        rw [show (k : ℤ) ^ 2 = ((K : ℕ) : ℤ) by rw [← hK]; push_cast; ring]
        omega
    · rintro d hd ⟨hev, s, hs⟩
      rcases hev with ⟨e, rfl⟩
      rw [show (s : ℤ) ^ 2 = ((s ^ 2 : ℕ) : ℤ) by push_cast; ring] at hs
      have hc : 2 * A088226_G k j = (if j % 2 = 1 then j - 1 else 2 * k + 2 - j) := by
        rcases Nat.mod_two_eq_zero_or_one j with hp | hp
        · rw [A088226_G_even hp, ite_eq_right (by omega)]
          omega
        · rw [A088226_G_odd hp, ite_eq_left hp]
          omega
      rw [hc] at hd
      -- Locate s^2 relative to k^2 and (k+1)^2.
      --
      rcases lt_trichotomy s k with hlt | rfl | hgt
      · have hb : s ^ 2 + 2 * k ≤ K + 1 := by
          have : s + 1 ≤ k := hlt
          nlinarith
        split_ifs at hd <;> omega
      · split_ifs at hd <;> omega
      · rcases Nat.lt_or_ge (k + 1) s with hgt2 | hle
        · have hb : K + 4 * k + 4 ≤ s ^ 2 := by
            have : k + 2 ≤ s := hgt2
            nlinarith
          split_ifs at hd <;> omega
        · obtain rfl : s = k + 1 := by omega
          rw [hK1] at hs
          split_ifs at hd <;> omega
  unfold A088226_f
  rw [key]
  omega

/-- Corrected form of the conjecture: a(n) = f(n - 1) for all n ≥ 1. -/
theorem A088226_main (n : ℕ) (hn : 1 ≤ n) : A088226_a n = A088226_f (n - 1) := by
  set k := Nat.sqrt (n - 1)
  have h1 : k ^ 2 ≤ n - 1 := Nat.sqrt_le' (n - 1)
  have h2 : n - 1 < (k + 1) ^ 2 := Nat.lt_succ_sqrt' (n - 1)
  have hK1 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  rw [A088226_block k n (by omega) (by omega)]
  rw [show n - 1 = k ^ 2 + (n - k ^ 2) - 1 by omega, A088226_f_block k _ (by omega) (by omega)]

/-- The conjecture as printed (a(n) = f(n)) fails at n = 2. -/
theorem A088226_literal_fails : A088226_a 2 = 0 ∧ A088226_f 2 = 1 := by
  refine ⟨by decide, ?_⟩
  have := A088226_f_block 1 2 (by norm_num) (by norm_num)
  simpa [A088226_G] using this
