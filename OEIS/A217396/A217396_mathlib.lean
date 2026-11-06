import Mathlib

/-
OEIS A217396 (Raphie Frank, 2012), data 1, 2, 3, 5, 7, 13 (keyword "full").
The entry's name is now "Prime indices of Euler's lucky numbers" (renamed 2025).
Original conjecture (OEIS wiki Talk:Conjectures/List): these are all k with
2^k - 2 (a) twice a triangular number, or (b) 3/2 times a tetrahedral number.

Definitions (k >= 1).
* `twiceTri k`: 2^k - 2 = n(n+1) for some n (twice the triangular number n(n+1)/2).
* `tetCond k`: 2 (2^k - 2) = 3 Te_j for some j, Te_j = j(j+1)(j+2)/6.

Main theorem.
* `A217396_main`: given Nagell's theorem (`RN`) and the bound `TetBound`
  (y^3 - y + 8 = 2^m implies m <= 50), for k >= 1:
  twiceTri k ∨ tetCond k  ↔  k ∈ {1, 2, 3, 5, 7, 13}.

Not checked in this file:
* `RN`: x^2 + 7 = 2^N only for N = 3, 4, 5, 7, 15 (Nagell 1948).
* `TetBound`: proved outside Lean by Matveev's lower bound for linear forms
  in three logarithms in Q(alpha), alpha^3 - alpha + 8 = 0, and Dujella-Petho
  reduction (PARI/GP, certificate/baker.gp, certificate/reduce.gp).
Checked here: the translation of both conditions to these equations, the
witnesses, and the finite exclusion for k <= 48 (strict monotonicity of
j(j+1)(j+2) and a bracketing j for each k).
-/

namespace A217396

def twiceTri (k : ℕ) : Prop := ∃ n : ℕ, 2 ^ k - 2 = n * (n + 1)

def tetCond (k : ℕ) : Prop := ∃ j : ℕ, 2 * (2 ^ k - 2) = 3 * (j * (j + 1) * (j + 2) / 6)

/-- Nagell (1948): the Ramanujan-Nagell equation. -/
def RN : Prop := ∀ x N : ℕ, x ^ 2 + 7 = 2 ^ N → N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 7 ∨ N = 15

/-- Proved outside Lean (Matveev + Dujella-Petho reduction). -/
def TetBound : Prop := ∀ (y : ℤ) (m : ℕ), y ^ 3 - y + 8 = 2 ^ m → m ≤ 50

theorem six_dvd (j : ℕ) : 6 ∣ j * (j + 1) * (j + 2) := by
  apply Nat.dvd_of_mod_eq_zero
  have h : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have : j * (j + 1) * (j + 2) % 6 = (j % 6) * ((j % 6) + 1) * ((j % 6) + 2) % 6 := by
    simp [Nat.mul_mod, Nat.add_mod]
  rw [this]
  interval_cases (j % 6) <;> rfl

theorem P_mono {a b : ℕ} (h : a ≤ b) : a * (a + 1) * (a + 2) ≤ b * (b + 1) * (b + 2) :=
  Nat.mul_le_mul (Nat.mul_le_mul h (by omega)) (by omega)

theorem noSol {T : ℕ} (J : ℕ) (h1 : J * (J + 1) * (J + 2) < T)
    (h2 : T < (J + 1) * (J + 1 + 1) * (J + 1 + 2)) (j : ℕ) : j * (j + 1) * (j + 2) ≠ T := by
  intro hj
  rcases Nat.lt_or_ge J j with h | h
  · have := P_mono (by omega : J + 1 ≤ j)
    omega
  · have := P_mono h
    omega

theorem two_le_pow {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem twiceTri_iff {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    2 ^ k - 2 = n * (n + 1) ↔ (2 * n + 1) ^ 2 + 7 = 2 ^ (k + 2) := by
  have h2 := two_le_pow hk
  rw [pow_add]
  constructor
  · intro h
    have : 2 ^ k = n * (n + 1) + 2 := by omega
    rw [this]; ring
  · intro h
    have : (2 * n + 1) ^ 2 + 7 = 4 * (n * (n + 1)) + 8 := by ring
    omega

theorem tetCond_iff {k : ℕ} (_hk : 1 ≤ k) (j : ℕ) :
    2 * (2 ^ k - 2) = 3 * (j * (j + 1) * (j + 2) / 6) ↔
      j * (j + 1) * (j + 2) = 4 * (2 ^ k - 2) := by
  obtain ⟨q, hq⟩ := six_dvd j
  rw [hq, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

theorem tet_to_cubic {k j : ℕ} (hk : 1 ≤ k) (h : j * (j + 1) * (j + 2) = 4 * (2 ^ k - 2)) :
    ((j : ℤ) + 1) ^ 3 - ((j : ℤ) + 1) + 8 = 2 ^ (k + 2) := by
  have h2 := two_le_pow hk
  have h' : (j : ℤ) * (j + 1) * (j + 2) = 4 * ((2 : ℤ) ^ k - 2) := by
    have := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast [Nat.cast_sub h2] at this
    exact this
  rw [pow_add]
  linear_combination h'

/-- **A217396**: assuming Nagell's theorem and `TetBound`, the k >= 1 with
2^k - 2 twice a triangular number or 3/2 times a tetrahedral number are exactly
1, 2, 3, 5, 7, 13 (the data of A217396). -/
theorem A217396_main (hRN : RN) (hT : TetBound) (k : ℕ) (hk : 1 ≤ k) :
    twiceTri k ∨ tetCond k ↔ k ∈ ({1, 2, 3, 5, 7, 13} : Finset ℕ) := by
  constructor
  · rintro (⟨n, hn⟩ | ⟨j, hj⟩)
    · have h := hRN _ _ ((twiceTri_iff hk n).mp hn)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · rw [tetCond_iff hk] at hj
      have hm := hT _ _ (tet_to_cubic hk hj)
      have hk48 : k ≤ 48 := by omega
      interval_cases k
      · simp
      · simp
      · simp
      · exact absurd hj (noSol 2 (by norm_num) (by norm_num) j)
      · simp
      · exact absurd hj (noSol 5 (by norm_num) (by norm_num) j)
      · simp
      · exact absurd hj (noSol 9 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 11 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 15 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 19 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 24 (by norm_num) (by norm_num) j)
      · simp
      · exact absurd hj (noSol 39 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 49 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 63 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 79 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 100 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 127 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 160 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 202 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 255 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 321 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 405 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 511 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 644 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 811 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 1023 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 1289 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 1624 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 2047 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 2579 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 3249 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 4095 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 5159 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 6500 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 8191 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 10320 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 13002 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 16383 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 20641 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 26006 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 32767 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 41284 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 52014 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 65535 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 82569 (by norm_num) (by norm_num) j)
      · exact absurd hj (noSol 104030 (by norm_num) (by norm_num) j)
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by norm_num⟩
    · exact Or.inl ⟨1, by norm_num⟩
    · exact Or.inl ⟨2, by norm_num⟩
    · exact Or.inl ⟨5, by norm_num⟩
    · exact Or.inr ⟨7, by norm_num⟩
    · exact Or.inl ⟨90, by norm_num⟩
