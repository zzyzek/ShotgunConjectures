/-
OEIS A217319 / A171949: the P-positions of Mark-4.

Mark-4 (Fraenkel): a position is n ≥ 0; a move goes from n to n - 1,
n - 2 or n - 3 (staying ≥ 0), or from n ≥ 1 to ⌊n/4⌋ (`A217319_move`).
The player unable to move loses. `A217319_isP n`: every move from n goes
to a position that is not a P-position (well-founded recursion, moves
decrease n).

Main theorem `A217319_main`: n is a P-position iff n = 0 or
n = 4^(2k+1) * m with m % 4 ≠ 0, i.e. iff n = 0 or the 4-adic valuation
of n is odd. So A171949 (P-positions of Mark-4, with 0 first) minus 0 is
A217319 (numbers whose binary expansion ends in 4k+2 or 4k+3 zeros), the
conjecture in both entries.

Proof: `A217319_D` is the recursive test D 0 = true, D n = !D (n/4) if
4 | n > 0, false otherwise. No move joins two D-positions
(`A217319_noPP`), and every non-D position has a move to a D-position
(`A217319_toP`): subtract n % 4 when 4 ∤ n, else divide by 4 (or, when
4 ∤ n and n - n % 4 fails D, divide by 4 from n directly). Then
isP = D by strong induction, and D n ↔ (n = 0 ∨ odd 4-adic valuation)
(`A217319_D_iff`).

Not checked: that the definition of Mark-4 transcribes Fraenkel's
(taken from Guo, arXiv:1108.1239, Sec. 1).
-/

/-- Moves of Mark-4: n → n - i (1 ≤ i ≤ 3, result ≥ 0) or n → ⌊n/4⌋ for n ≥ 1. -/
def A217319_move (n m : Nat) : Prop := (m < n ∧ n ≤ m + 3) ∨ (0 < n ∧ m = n / 4)

theorem A217319_move_lt {n m : Nat} (h : A217319_move n m) : m < n := by
  unfold A217319_move at h; omega

/-- P-positions: every move leads to a non-P-position. -/
def A217319_isP (n : Nat) : Prop := ∀ m, (h : m < n) → A217319_move n m → ¬ A217319_isP m
termination_by n

/-- Recursive test: D 0 = true; D n = !D (n/4) if 4 ∣ n > 0; else false. -/
def A217319_D (n : Nat) : Bool :=
  if h : n = 0 then true else if n % 4 = 0 then !A217319_D (n / 4) else false
termination_by n
decreasing_by omega

theorem A217319_D_zero : A217319_D 0 = true := by
  rw [A217319_D]; simp

theorem A217319_D_ndvd {n : Nat} (h : n % 4 ≠ 0) : A217319_D n = false := by
  rw [A217319_D]
  have h0 : n ≠ 0 := by omega
  simp [h0, h]

theorem A217319_D_mul4 {q : Nat} (hq : 0 < q) : A217319_D (4 * q) = !A217319_D q := by
  rw [A217319_D]
  have h0 : 4 * q ≠ 0 := by omega
  have h4 : 4 * q % 4 = 0 := by omega
  have hd : 4 * q / 4 = q := by omega
  simp [h0, h4, hd]

/-- No move from a D-position to a D-position. -/
theorem A217319_noPP {n m : Nat} (hn : A217319_D n = true) (hmv : A217319_move n m) :
    A217319_D m = false := by
  by_cases h0 : n = 0
  · have := A217319_move_lt hmv; omega
  have h4 : n % 4 = 0 := by
    by_cases h : n % 4 = 0
    · exact h
    · rw [A217319_D_ndvd h] at hn; exact absurd hn (by decide)
  have hq : n = 4 * (n / 4) := by omega
  have hqpos : 0 < n / 4 := by omega
  have hDq : A217319_D (n / 4) = false := by
    rw [hq, A217319_D_mul4 hqpos] at hn
    revert hn; cases A217319_D (n / 4) <;> simp
  unfold A217319_move at hmv
  rcases hmv with ⟨h1, h2⟩ | ⟨_, h2⟩
  · exact A217319_D_ndvd (by omega)
  · rw [h2]; exact hDq

/-- Every non-D position has a move to a D-position. -/
theorem A217319_toP {n : Nat} (hn : A217319_D n = false) :
    ∃ m, A217319_move n m ∧ A217319_D m = true := by
  have h0 : n ≠ 0 := by
    intro h; rw [h, A217319_D_zero] at hn; exact absurd hn (by decide)
  by_cases h4 : n % 4 = 0
  · refine ⟨n / 4, Or.inr ⟨by omega, rfl⟩, ?_⟩
    have hq : n = 4 * (n / 4) := by omega
    rw [hq, A217319_D_mul4 (by omega)] at hn
    revert hn; cases A217319_D (n / 4) <;> simp
  · cases hr : A217319_D (n - n % 4) with
    | true => exact ⟨n - n % 4, Or.inl ⟨by omega, by omega⟩, hr⟩
    | false =>
      refine ⟨n / 4, Or.inr ⟨by omega, rfl⟩, ?_⟩
      by_cases hz : n / 4 = 0
      · rw [hz]; exact A217319_D_zero
      have he : n - n % 4 = 4 * (n / 4) := by omega
      rw [he, A217319_D_mul4 (by omega)] at hr
      revert hr; cases A217319_D (n / 4) <;> simp

/-- The P-positions of Mark-4 are exactly the D-positions. -/
theorem A217319_isP_iff_D (n : Nat) : A217319_isP n ↔ A217319_D n = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [A217319_isP]
    constructor
    · intro hP
      cases hD : A217319_D n with
      | true => rfl
      | false =>
        obtain ⟨m, hmv, hm⟩ := A217319_toP hD
        have hlt := A217319_move_lt hmv
        exact absurd ((ih m hlt).mpr hm) (hP m hlt hmv)
    · intro hD m hlt hmv hPm
      have := A217319_noPP hD hmv
      rw [(ih m hlt).mp hPm] at this
      exact absurd this (by decide)

/-- D (4^j * m) = (j odd) for m % 4 ≠ 0. -/
theorem A217319_D_pow (m : Nat) (hm : m % 4 ≠ 0) :
    ∀ j, A217319_D (4 ^ j * m) = (j % 2 == 1) := by
  intro j
  induction j with
  | zero => simp [A217319_D_ndvd hm]
  | succ j ih =>
    have hpos : 0 < 4 ^ j * m := Nat.mul_pos (Nat.pos_of_ne_zero (by simp)) (by omega)
    rw [Nat.pow_succ, Nat.mul_comm (4 ^ j) 4, Nat.mul_assoc, A217319_D_mul4 hpos, ih]
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have : (j + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (j + 1) % 2 = 0 := by omega
      simp [h, this]

/-- Every n > 0 is 4^j * m with m % 4 ≠ 0. -/
theorem A217319_decomp (n : Nat) (hn : 0 < n) : ∃ j m, m % 4 ≠ 0 ∧ n = 4 ^ j * m := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h4 : n % 4 = 0
    · obtain ⟨j, m, hm, he⟩ := ih (n / 4) (by omega) (by omega)
      refine ⟨j + 1, m, hm, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (4 ^ j) 4, Nat.mul_assoc, ← he]
      omega
    · exact ⟨0, n, h4, by simp⟩

/-- D n ↔ n = 0 or the 4-adic valuation of n is odd. -/
theorem A217319_D_iff (n : Nat) :
    A217319_D n = true ↔ (n = 0 ∨ ∃ k m, m % 4 ≠ 0 ∧ n = 4 ^ (2 * k + 1) * m) := by
  constructor
  · intro hD
    by_cases h0 : n = 0
    · exact Or.inl h0
    · obtain ⟨j, m, hm, he⟩ := A217319_decomp n (by omega)
      rw [he, A217319_D_pow m hm j] at hD
      have hj : j % 2 = 1 := by simpa using hD
      exact Or.inr ⟨j / 2, m, hm, by rw [he]; congr 2; omega⟩
  · rintro (h | ⟨k, m, hm, he⟩)
    · rw [h]; exact A217319_D_zero
    · rw [he, A217319_D_pow m hm]
      have : (2 * k + 1) % 2 = 1 := by omega
      simp [this]

/-- Main theorem: the P-positions of Mark-4 are 0 and the numbers with odd
4-adic valuation (A171949 = {0} ∪ A217319). -/
theorem A217319_main (n : Nat) :
    A217319_isP n ↔ (n = 0 ∨ ∃ k m, m % 4 ≠ 0 ∧ n = 4 ^ (2 * k + 1) * m) :=
  (A217319_isP_iff_D n).trans (A217319_D_iff n)
