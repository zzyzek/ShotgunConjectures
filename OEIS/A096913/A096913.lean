/-
OEIS A096913: numbers k such that (largest digit of k)^(smallest digit of k) + k is a
square.  Comment: "Conjecture: 0 and 3844 are the only squares in this sequence."
(Maon Wenders, 2012, reports an exhaustive search confirming it.)

Checked here, for all k:
  * `A096913_squares`: if k = s*s and k + maxD(k)^minD(k) = t*t then k = 0 or k = 3844;
  * `A096913_3844`: 3844 = 62^2 is a term (8^3 + 3844 = 66^2), and so is 0 (0^0 + 0 = 1).
Argument: d = maxD^minD >= 1, so t = s + j with j >= 1 and d = j (2s + j).  Then j*j <= d,
d / j = 2s + j, and s = (d/j - j)/2.  For each of the 100 pairs (a, b) with a, b <= 9 (a = 0 forces k = 0),
the loops `chkR` run over all j <= isqrt(a^b) and test every candidate s.
Digits are base 10 via `digs` (0 has the single digit 0).  Not checked here: nothing
beyond reading the definition.
-/

-- Base-10 digits (least significant first); fuel is the number itself.
--
def digsF : Nat → Nat → List Nat
  | 0, _ => [0]
  | f + 1, n => if n < 10 then [n] else (n % 10) :: digsF f (n / 10)

def digs (n : Nat) : List Nat := digsF (n + 1) n

def maxD (n : Nat) : Nat := (digs n).foldl max 0
def minD (n : Nat) : Nat := (digs n).foldl min 9

-- Candidate test for d = a^b and t - s = j.
--
def good (d a b j : Nat) : Bool :=
  if d % j == 0 && (d / j - j) % 2 == 0 && j ≤ d / j then
    let s := (d / j - j) / 2
    maxD (s * s) != a || minD (s * s) != b || s * s == 0 || s * s == 3844
  else true

def chkR (d a b lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => good d a b (lo + n + 1) && chkR d a b lo n

theorem chkR_spec (d a b lo : Nat) : ∀ n, chkR d a b lo n = true → ∀ j, lo < j →
    j ≤ lo + n → good d a b j = true := by
  intro n
  induction n with
  | zero => intro _ j h1 h2; omega
  | succ n ih =>
    intro h j h1 h2
    simp only [chkR, Bool.and_eq_true] at h
    by_cases hj : j = lo + n + 1
    · subst hj; exact h.1
    · exact ih h.2 j h1 (by omega)

def tbl : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 8, 11, 16, 22, 1, 1, 3, 5, 9, 15, 27, 46, 81, 140, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1, 2, 5, 11, 25, 55, 125, 279, 625, 1397, 1, 2, 6, 14, 36, 88, 216, 529, 1296, 3174, 1, 2, 7, 18, 49, 129, 343, 907, 2401, 6352, 1, 2, 8, 22, 64, 181, 512, 1448, 4096, 11585, 1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683]

def J (a b : Nat) : Nat := tbl.getD (10 * a + b) 0

-- The finite check, one theorem per (a, b) and chunk of at most 5000 values of j.
--
theorem J_0_0 : J 0 0 = 1 ∧ J 0 0 * J 0 0 ≤ 0 ^ 0 ∧ 0 ^ 0 < (J 0 0 + 1) * (J 0 0 + 1) := by decide
theorem c_0_0_0 : chkR (0 ^ 0) 0 0 0 1 = true := by decide +kernel
theorem g_0_0 : ∀ j, 1 ≤ j → j ≤ J 0 0 → good (0 ^ 0) 0 0 j = true := by
  intro j h1 h2
  have hJ := J_0_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_0_0_0 j (by omega) (by omega)
  omega

theorem J_0_1 : J 0 1 = 0 ∧ J 0 1 * J 0 1 ≤ 0 ^ 1 ∧ 0 ^ 1 < (J 0 1 + 1) * (J 0 1 + 1) := by decide
theorem g_0_1 : ∀ j, 1 ≤ j → j ≤ J 0 1 → good (0 ^ 1) 0 1 j = true := by
  intro j h1 h2; have := J_0_1.1; omega

theorem J_0_2 : J 0 2 = 0 ∧ J 0 2 * J 0 2 ≤ 0 ^ 2 ∧ 0 ^ 2 < (J 0 2 + 1) * (J 0 2 + 1) := by decide
theorem g_0_2 : ∀ j, 1 ≤ j → j ≤ J 0 2 → good (0 ^ 2) 0 2 j = true := by
  intro j h1 h2; have := J_0_2.1; omega

theorem J_0_3 : J 0 3 = 0 ∧ J 0 3 * J 0 3 ≤ 0 ^ 3 ∧ 0 ^ 3 < (J 0 3 + 1) * (J 0 3 + 1) := by decide
theorem g_0_3 : ∀ j, 1 ≤ j → j ≤ J 0 3 → good (0 ^ 3) 0 3 j = true := by
  intro j h1 h2; have := J_0_3.1; omega

theorem J_0_4 : J 0 4 = 0 ∧ J 0 4 * J 0 4 ≤ 0 ^ 4 ∧ 0 ^ 4 < (J 0 4 + 1) * (J 0 4 + 1) := by decide
theorem g_0_4 : ∀ j, 1 ≤ j → j ≤ J 0 4 → good (0 ^ 4) 0 4 j = true := by
  intro j h1 h2; have := J_0_4.1; omega

theorem J_0_5 : J 0 5 = 0 ∧ J 0 5 * J 0 5 ≤ 0 ^ 5 ∧ 0 ^ 5 < (J 0 5 + 1) * (J 0 5 + 1) := by decide
theorem g_0_5 : ∀ j, 1 ≤ j → j ≤ J 0 5 → good (0 ^ 5) 0 5 j = true := by
  intro j h1 h2; have := J_0_5.1; omega

theorem J_0_6 : J 0 6 = 0 ∧ J 0 6 * J 0 6 ≤ 0 ^ 6 ∧ 0 ^ 6 < (J 0 6 + 1) * (J 0 6 + 1) := by decide
theorem g_0_6 : ∀ j, 1 ≤ j → j ≤ J 0 6 → good (0 ^ 6) 0 6 j = true := by
  intro j h1 h2; have := J_0_6.1; omega

theorem J_0_7 : J 0 7 = 0 ∧ J 0 7 * J 0 7 ≤ 0 ^ 7 ∧ 0 ^ 7 < (J 0 7 + 1) * (J 0 7 + 1) := by decide
theorem g_0_7 : ∀ j, 1 ≤ j → j ≤ J 0 7 → good (0 ^ 7) 0 7 j = true := by
  intro j h1 h2; have := J_0_7.1; omega

theorem J_0_8 : J 0 8 = 0 ∧ J 0 8 * J 0 8 ≤ 0 ^ 8 ∧ 0 ^ 8 < (J 0 8 + 1) * (J 0 8 + 1) := by decide
theorem g_0_8 : ∀ j, 1 ≤ j → j ≤ J 0 8 → good (0 ^ 8) 0 8 j = true := by
  intro j h1 h2; have := J_0_8.1; omega

theorem J_0_9 : J 0 9 = 0 ∧ J 0 9 * J 0 9 ≤ 0 ^ 9 ∧ 0 ^ 9 < (J 0 9 + 1) * (J 0 9 + 1) := by decide
theorem g_0_9 : ∀ j, 1 ≤ j → j ≤ J 0 9 → good (0 ^ 9) 0 9 j = true := by
  intro j h1 h2; have := J_0_9.1; omega

theorem J_1_0 : J 1 0 = 1 ∧ J 1 0 * J 1 0 ≤ 1 ^ 0 ∧ 1 ^ 0 < (J 1 0 + 1) * (J 1 0 + 1) := by decide
theorem c_1_0_0 : chkR (1 ^ 0) 1 0 0 1 = true := by decide +kernel
theorem g_1_0 : ∀ j, 1 ≤ j → j ≤ J 1 0 → good (1 ^ 0) 1 0 j = true := by
  intro j h1 h2
  have hJ := J_1_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_0_0 j (by omega) (by omega)
  omega

theorem J_1_1 : J 1 1 = 1 ∧ J 1 1 * J 1 1 ≤ 1 ^ 1 ∧ 1 ^ 1 < (J 1 1 + 1) * (J 1 1 + 1) := by decide
theorem c_1_1_0 : chkR (1 ^ 1) 1 1 0 1 = true := by decide +kernel
theorem g_1_1 : ∀ j, 1 ≤ j → j ≤ J 1 1 → good (1 ^ 1) 1 1 j = true := by
  intro j h1 h2
  have hJ := J_1_1.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_1_0 j (by omega) (by omega)
  omega

theorem J_1_2 : J 1 2 = 1 ∧ J 1 2 * J 1 2 ≤ 1 ^ 2 ∧ 1 ^ 2 < (J 1 2 + 1) * (J 1 2 + 1) := by decide
theorem c_1_2_0 : chkR (1 ^ 2) 1 2 0 1 = true := by decide +kernel
theorem g_1_2 : ∀ j, 1 ≤ j → j ≤ J 1 2 → good (1 ^ 2) 1 2 j = true := by
  intro j h1 h2
  have hJ := J_1_2.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_2_0 j (by omega) (by omega)
  omega

theorem J_1_3 : J 1 3 = 1 ∧ J 1 3 * J 1 3 ≤ 1 ^ 3 ∧ 1 ^ 3 < (J 1 3 + 1) * (J 1 3 + 1) := by decide
theorem c_1_3_0 : chkR (1 ^ 3) 1 3 0 1 = true := by decide +kernel
theorem g_1_3 : ∀ j, 1 ≤ j → j ≤ J 1 3 → good (1 ^ 3) 1 3 j = true := by
  intro j h1 h2
  have hJ := J_1_3.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_3_0 j (by omega) (by omega)
  omega

theorem J_1_4 : J 1 4 = 1 ∧ J 1 4 * J 1 4 ≤ 1 ^ 4 ∧ 1 ^ 4 < (J 1 4 + 1) * (J 1 4 + 1) := by decide
theorem c_1_4_0 : chkR (1 ^ 4) 1 4 0 1 = true := by decide +kernel
theorem g_1_4 : ∀ j, 1 ≤ j → j ≤ J 1 4 → good (1 ^ 4) 1 4 j = true := by
  intro j h1 h2
  have hJ := J_1_4.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_4_0 j (by omega) (by omega)
  omega

theorem J_1_5 : J 1 5 = 1 ∧ J 1 5 * J 1 5 ≤ 1 ^ 5 ∧ 1 ^ 5 < (J 1 5 + 1) * (J 1 5 + 1) := by decide
theorem c_1_5_0 : chkR (1 ^ 5) 1 5 0 1 = true := by decide +kernel
theorem g_1_5 : ∀ j, 1 ≤ j → j ≤ J 1 5 → good (1 ^ 5) 1 5 j = true := by
  intro j h1 h2
  have hJ := J_1_5.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_5_0 j (by omega) (by omega)
  omega

theorem J_1_6 : J 1 6 = 1 ∧ J 1 6 * J 1 6 ≤ 1 ^ 6 ∧ 1 ^ 6 < (J 1 6 + 1) * (J 1 6 + 1) := by decide
theorem c_1_6_0 : chkR (1 ^ 6) 1 6 0 1 = true := by decide +kernel
theorem g_1_6 : ∀ j, 1 ≤ j → j ≤ J 1 6 → good (1 ^ 6) 1 6 j = true := by
  intro j h1 h2
  have hJ := J_1_6.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_6_0 j (by omega) (by omega)
  omega

theorem J_1_7 : J 1 7 = 1 ∧ J 1 7 * J 1 7 ≤ 1 ^ 7 ∧ 1 ^ 7 < (J 1 7 + 1) * (J 1 7 + 1) := by decide
theorem c_1_7_0 : chkR (1 ^ 7) 1 7 0 1 = true := by decide +kernel
theorem g_1_7 : ∀ j, 1 ≤ j → j ≤ J 1 7 → good (1 ^ 7) 1 7 j = true := by
  intro j h1 h2
  have hJ := J_1_7.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_7_0 j (by omega) (by omega)
  omega

theorem J_1_8 : J 1 8 = 1 ∧ J 1 8 * J 1 8 ≤ 1 ^ 8 ∧ 1 ^ 8 < (J 1 8 + 1) * (J 1 8 + 1) := by decide
theorem c_1_8_0 : chkR (1 ^ 8) 1 8 0 1 = true := by decide +kernel
theorem g_1_8 : ∀ j, 1 ≤ j → j ≤ J 1 8 → good (1 ^ 8) 1 8 j = true := by
  intro j h1 h2
  have hJ := J_1_8.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_8_0 j (by omega) (by omega)
  omega

theorem J_1_9 : J 1 9 = 1 ∧ J 1 9 * J 1 9 ≤ 1 ^ 9 ∧ 1 ^ 9 < (J 1 9 + 1) * (J 1 9 + 1) := by decide
theorem c_1_9_0 : chkR (1 ^ 9) 1 9 0 1 = true := by decide +kernel
theorem g_1_9 : ∀ j, 1 ≤ j → j ≤ J 1 9 → good (1 ^ 9) 1 9 j = true := by
  intro j h1 h2
  have hJ := J_1_9.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_1_9_0 j (by omega) (by omega)
  omega

theorem J_2_0 : J 2 0 = 1 ∧ J 2 0 * J 2 0 ≤ 2 ^ 0 ∧ 2 ^ 0 < (J 2 0 + 1) * (J 2 0 + 1) := by decide
theorem c_2_0_0 : chkR (2 ^ 0) 2 0 0 1 = true := by decide +kernel
theorem g_2_0 : ∀ j, 1 ≤ j → j ≤ J 2 0 → good (2 ^ 0) 2 0 j = true := by
  intro j h1 h2
  have hJ := J_2_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_2_0_0 j (by omega) (by omega)
  omega

theorem J_2_1 : J 2 1 = 1 ∧ J 2 1 * J 2 1 ≤ 2 ^ 1 ∧ 2 ^ 1 < (J 2 1 + 1) * (J 2 1 + 1) := by decide
theorem c_2_1_0 : chkR (2 ^ 1) 2 1 0 1 = true := by decide +kernel
theorem g_2_1 : ∀ j, 1 ≤ j → j ≤ J 2 1 → good (2 ^ 1) 2 1 j = true := by
  intro j h1 h2
  have hJ := J_2_1.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_2_1_0 j (by omega) (by omega)
  omega

theorem J_2_2 : J 2 2 = 2 ∧ J 2 2 * J 2 2 ≤ 2 ^ 2 ∧ 2 ^ 2 < (J 2 2 + 1) * (J 2 2 + 1) := by decide
theorem c_2_2_0 : chkR (2 ^ 2) 2 2 0 2 = true := by decide +kernel
theorem g_2_2 : ∀ j, 1 ≤ j → j ≤ J 2 2 → good (2 ^ 2) 2 2 j = true := by
  intro j h1 h2
  have hJ := J_2_2.1
  by_cases h0 : j ≤ 2
  · exact chkR_spec _ _ _ _ _ c_2_2_0 j (by omega) (by omega)
  omega

theorem J_2_3 : J 2 3 = 2 ∧ J 2 3 * J 2 3 ≤ 2 ^ 3 ∧ 2 ^ 3 < (J 2 3 + 1) * (J 2 3 + 1) := by decide
theorem c_2_3_0 : chkR (2 ^ 3) 2 3 0 2 = true := by decide +kernel
theorem g_2_3 : ∀ j, 1 ≤ j → j ≤ J 2 3 → good (2 ^ 3) 2 3 j = true := by
  intro j h1 h2
  have hJ := J_2_3.1
  by_cases h0 : j ≤ 2
  · exact chkR_spec _ _ _ _ _ c_2_3_0 j (by omega) (by omega)
  omega

theorem J_2_4 : J 2 4 = 4 ∧ J 2 4 * J 2 4 ≤ 2 ^ 4 ∧ 2 ^ 4 < (J 2 4 + 1) * (J 2 4 + 1) := by decide
theorem c_2_4_0 : chkR (2 ^ 4) 2 4 0 4 = true := by decide +kernel
theorem g_2_4 : ∀ j, 1 ≤ j → j ≤ J 2 4 → good (2 ^ 4) 2 4 j = true := by
  intro j h1 h2
  have hJ := J_2_4.1
  by_cases h0 : j ≤ 4
  · exact chkR_spec _ _ _ _ _ c_2_4_0 j (by omega) (by omega)
  omega

theorem J_2_5 : J 2 5 = 5 ∧ J 2 5 * J 2 5 ≤ 2 ^ 5 ∧ 2 ^ 5 < (J 2 5 + 1) * (J 2 5 + 1) := by decide
theorem c_2_5_0 : chkR (2 ^ 5) 2 5 0 5 = true := by decide +kernel
theorem g_2_5 : ∀ j, 1 ≤ j → j ≤ J 2 5 → good (2 ^ 5) 2 5 j = true := by
  intro j h1 h2
  have hJ := J_2_5.1
  by_cases h0 : j ≤ 5
  · exact chkR_spec _ _ _ _ _ c_2_5_0 j (by omega) (by omega)
  omega

theorem J_2_6 : J 2 6 = 8 ∧ J 2 6 * J 2 6 ≤ 2 ^ 6 ∧ 2 ^ 6 < (J 2 6 + 1) * (J 2 6 + 1) := by decide
theorem c_2_6_0 : chkR (2 ^ 6) 2 6 0 8 = true := by decide +kernel
theorem g_2_6 : ∀ j, 1 ≤ j → j ≤ J 2 6 → good (2 ^ 6) 2 6 j = true := by
  intro j h1 h2
  have hJ := J_2_6.1
  by_cases h0 : j ≤ 8
  · exact chkR_spec _ _ _ _ _ c_2_6_0 j (by omega) (by omega)
  omega

theorem J_2_7 : J 2 7 = 11 ∧ J 2 7 * J 2 7 ≤ 2 ^ 7 ∧ 2 ^ 7 < (J 2 7 + 1) * (J 2 7 + 1) := by decide
theorem c_2_7_0 : chkR (2 ^ 7) 2 7 0 11 = true := by decide +kernel
theorem g_2_7 : ∀ j, 1 ≤ j → j ≤ J 2 7 → good (2 ^ 7) 2 7 j = true := by
  intro j h1 h2
  have hJ := J_2_7.1
  by_cases h0 : j ≤ 11
  · exact chkR_spec _ _ _ _ _ c_2_7_0 j (by omega) (by omega)
  omega

theorem J_2_8 : J 2 8 = 16 ∧ J 2 8 * J 2 8 ≤ 2 ^ 8 ∧ 2 ^ 8 < (J 2 8 + 1) * (J 2 8 + 1) := by decide
theorem c_2_8_0 : chkR (2 ^ 8) 2 8 0 16 = true := by decide +kernel
theorem g_2_8 : ∀ j, 1 ≤ j → j ≤ J 2 8 → good (2 ^ 8) 2 8 j = true := by
  intro j h1 h2
  have hJ := J_2_8.1
  by_cases h0 : j ≤ 16
  · exact chkR_spec _ _ _ _ _ c_2_8_0 j (by omega) (by omega)
  omega

theorem J_2_9 : J 2 9 = 22 ∧ J 2 9 * J 2 9 ≤ 2 ^ 9 ∧ 2 ^ 9 < (J 2 9 + 1) * (J 2 9 + 1) := by decide
theorem c_2_9_0 : chkR (2 ^ 9) 2 9 0 22 = true := by decide +kernel
theorem g_2_9 : ∀ j, 1 ≤ j → j ≤ J 2 9 → good (2 ^ 9) 2 9 j = true := by
  intro j h1 h2
  have hJ := J_2_9.1
  by_cases h0 : j ≤ 22
  · exact chkR_spec _ _ _ _ _ c_2_9_0 j (by omega) (by omega)
  omega

theorem J_3_0 : J 3 0 = 1 ∧ J 3 0 * J 3 0 ≤ 3 ^ 0 ∧ 3 ^ 0 < (J 3 0 + 1) * (J 3 0 + 1) := by decide
theorem c_3_0_0 : chkR (3 ^ 0) 3 0 0 1 = true := by decide +kernel
theorem g_3_0 : ∀ j, 1 ≤ j → j ≤ J 3 0 → good (3 ^ 0) 3 0 j = true := by
  intro j h1 h2
  have hJ := J_3_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_3_0_0 j (by omega) (by omega)
  omega

theorem J_3_1 : J 3 1 = 1 ∧ J 3 1 * J 3 1 ≤ 3 ^ 1 ∧ 3 ^ 1 < (J 3 1 + 1) * (J 3 1 + 1) := by decide
theorem c_3_1_0 : chkR (3 ^ 1) 3 1 0 1 = true := by decide +kernel
theorem g_3_1 : ∀ j, 1 ≤ j → j ≤ J 3 1 → good (3 ^ 1) 3 1 j = true := by
  intro j h1 h2
  have hJ := J_3_1.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_3_1_0 j (by omega) (by omega)
  omega

theorem J_3_2 : J 3 2 = 3 ∧ J 3 2 * J 3 2 ≤ 3 ^ 2 ∧ 3 ^ 2 < (J 3 2 + 1) * (J 3 2 + 1) := by decide
theorem c_3_2_0 : chkR (3 ^ 2) 3 2 0 3 = true := by decide +kernel
theorem g_3_2 : ∀ j, 1 ≤ j → j ≤ J 3 2 → good (3 ^ 2) 3 2 j = true := by
  intro j h1 h2
  have hJ := J_3_2.1
  by_cases h0 : j ≤ 3
  · exact chkR_spec _ _ _ _ _ c_3_2_0 j (by omega) (by omega)
  omega

theorem J_3_3 : J 3 3 = 5 ∧ J 3 3 * J 3 3 ≤ 3 ^ 3 ∧ 3 ^ 3 < (J 3 3 + 1) * (J 3 3 + 1) := by decide
theorem c_3_3_0 : chkR (3 ^ 3) 3 3 0 5 = true := by decide +kernel
theorem g_3_3 : ∀ j, 1 ≤ j → j ≤ J 3 3 → good (3 ^ 3) 3 3 j = true := by
  intro j h1 h2
  have hJ := J_3_3.1
  by_cases h0 : j ≤ 5
  · exact chkR_spec _ _ _ _ _ c_3_3_0 j (by omega) (by omega)
  omega

theorem J_3_4 : J 3 4 = 9 ∧ J 3 4 * J 3 4 ≤ 3 ^ 4 ∧ 3 ^ 4 < (J 3 4 + 1) * (J 3 4 + 1) := by decide
theorem c_3_4_0 : chkR (3 ^ 4) 3 4 0 9 = true := by decide +kernel
theorem g_3_4 : ∀ j, 1 ≤ j → j ≤ J 3 4 → good (3 ^ 4) 3 4 j = true := by
  intro j h1 h2
  have hJ := J_3_4.1
  by_cases h0 : j ≤ 9
  · exact chkR_spec _ _ _ _ _ c_3_4_0 j (by omega) (by omega)
  omega

theorem J_3_5 : J 3 5 = 15 ∧ J 3 5 * J 3 5 ≤ 3 ^ 5 ∧ 3 ^ 5 < (J 3 5 + 1) * (J 3 5 + 1) := by decide
theorem c_3_5_0 : chkR (3 ^ 5) 3 5 0 15 = true := by decide +kernel
theorem g_3_5 : ∀ j, 1 ≤ j → j ≤ J 3 5 → good (3 ^ 5) 3 5 j = true := by
  intro j h1 h2
  have hJ := J_3_5.1
  by_cases h0 : j ≤ 15
  · exact chkR_spec _ _ _ _ _ c_3_5_0 j (by omega) (by omega)
  omega

theorem J_3_6 : J 3 6 = 27 ∧ J 3 6 * J 3 6 ≤ 3 ^ 6 ∧ 3 ^ 6 < (J 3 6 + 1) * (J 3 6 + 1) := by decide
theorem c_3_6_0 : chkR (3 ^ 6) 3 6 0 27 = true := by decide +kernel
theorem g_3_6 : ∀ j, 1 ≤ j → j ≤ J 3 6 → good (3 ^ 6) 3 6 j = true := by
  intro j h1 h2
  have hJ := J_3_6.1
  by_cases h0 : j ≤ 27
  · exact chkR_spec _ _ _ _ _ c_3_6_0 j (by omega) (by omega)
  omega

theorem J_3_7 : J 3 7 = 46 ∧ J 3 7 * J 3 7 ≤ 3 ^ 7 ∧ 3 ^ 7 < (J 3 7 + 1) * (J 3 7 + 1) := by decide
theorem c_3_7_0 : chkR (3 ^ 7) 3 7 0 46 = true := by decide +kernel
theorem g_3_7 : ∀ j, 1 ≤ j → j ≤ J 3 7 → good (3 ^ 7) 3 7 j = true := by
  intro j h1 h2
  have hJ := J_3_7.1
  by_cases h0 : j ≤ 46
  · exact chkR_spec _ _ _ _ _ c_3_7_0 j (by omega) (by omega)
  omega

theorem J_3_8 : J 3 8 = 81 ∧ J 3 8 * J 3 8 ≤ 3 ^ 8 ∧ 3 ^ 8 < (J 3 8 + 1) * (J 3 8 + 1) := by decide
theorem c_3_8_0 : chkR (3 ^ 8) 3 8 0 81 = true := by decide +kernel
theorem g_3_8 : ∀ j, 1 ≤ j → j ≤ J 3 8 → good (3 ^ 8) 3 8 j = true := by
  intro j h1 h2
  have hJ := J_3_8.1
  by_cases h0 : j ≤ 81
  · exact chkR_spec _ _ _ _ _ c_3_8_0 j (by omega) (by omega)
  omega

theorem J_3_9 : J 3 9 = 140 ∧ J 3 9 * J 3 9 ≤ 3 ^ 9 ∧ 3 ^ 9 < (J 3 9 + 1) * (J 3 9 + 1) := by decide
theorem c_3_9_0 : chkR (3 ^ 9) 3 9 0 140 = true := by decide +kernel
theorem g_3_9 : ∀ j, 1 ≤ j → j ≤ J 3 9 → good (3 ^ 9) 3 9 j = true := by
  intro j h1 h2
  have hJ := J_3_9.1
  by_cases h0 : j ≤ 140
  · exact chkR_spec _ _ _ _ _ c_3_9_0 j (by omega) (by omega)
  omega

theorem J_4_0 : J 4 0 = 1 ∧ J 4 0 * J 4 0 ≤ 4 ^ 0 ∧ 4 ^ 0 < (J 4 0 + 1) * (J 4 0 + 1) := by decide
theorem c_4_0_0 : chkR (4 ^ 0) 4 0 0 1 = true := by decide +kernel
theorem g_4_0 : ∀ j, 1 ≤ j → j ≤ J 4 0 → good (4 ^ 0) 4 0 j = true := by
  intro j h1 h2
  have hJ := J_4_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_4_0_0 j (by omega) (by omega)
  omega

theorem J_4_1 : J 4 1 = 2 ∧ J 4 1 * J 4 1 ≤ 4 ^ 1 ∧ 4 ^ 1 < (J 4 1 + 1) * (J 4 1 + 1) := by decide
theorem c_4_1_0 : chkR (4 ^ 1) 4 1 0 2 = true := by decide +kernel
theorem g_4_1 : ∀ j, 1 ≤ j → j ≤ J 4 1 → good (4 ^ 1) 4 1 j = true := by
  intro j h1 h2
  have hJ := J_4_1.1
  by_cases h0 : j ≤ 2
  · exact chkR_spec _ _ _ _ _ c_4_1_0 j (by omega) (by omega)
  omega

theorem J_4_2 : J 4 2 = 4 ∧ J 4 2 * J 4 2 ≤ 4 ^ 2 ∧ 4 ^ 2 < (J 4 2 + 1) * (J 4 2 + 1) := by decide
theorem c_4_2_0 : chkR (4 ^ 2) 4 2 0 4 = true := by decide +kernel
theorem g_4_2 : ∀ j, 1 ≤ j → j ≤ J 4 2 → good (4 ^ 2) 4 2 j = true := by
  intro j h1 h2
  have hJ := J_4_2.1
  by_cases h0 : j ≤ 4
  · exact chkR_spec _ _ _ _ _ c_4_2_0 j (by omega) (by omega)
  omega

theorem J_4_3 : J 4 3 = 8 ∧ J 4 3 * J 4 3 ≤ 4 ^ 3 ∧ 4 ^ 3 < (J 4 3 + 1) * (J 4 3 + 1) := by decide
theorem c_4_3_0 : chkR (4 ^ 3) 4 3 0 8 = true := by decide +kernel
theorem g_4_3 : ∀ j, 1 ≤ j → j ≤ J 4 3 → good (4 ^ 3) 4 3 j = true := by
  intro j h1 h2
  have hJ := J_4_3.1
  by_cases h0 : j ≤ 8
  · exact chkR_spec _ _ _ _ _ c_4_3_0 j (by omega) (by omega)
  omega

theorem J_4_4 : J 4 4 = 16 ∧ J 4 4 * J 4 4 ≤ 4 ^ 4 ∧ 4 ^ 4 < (J 4 4 + 1) * (J 4 4 + 1) := by decide
theorem c_4_4_0 : chkR (4 ^ 4) 4 4 0 16 = true := by decide +kernel
theorem g_4_4 : ∀ j, 1 ≤ j → j ≤ J 4 4 → good (4 ^ 4) 4 4 j = true := by
  intro j h1 h2
  have hJ := J_4_4.1
  by_cases h0 : j ≤ 16
  · exact chkR_spec _ _ _ _ _ c_4_4_0 j (by omega) (by omega)
  omega

theorem J_4_5 : J 4 5 = 32 ∧ J 4 5 * J 4 5 ≤ 4 ^ 5 ∧ 4 ^ 5 < (J 4 5 + 1) * (J 4 5 + 1) := by decide
theorem c_4_5_0 : chkR (4 ^ 5) 4 5 0 32 = true := by decide +kernel
theorem g_4_5 : ∀ j, 1 ≤ j → j ≤ J 4 5 → good (4 ^ 5) 4 5 j = true := by
  intro j h1 h2
  have hJ := J_4_5.1
  by_cases h0 : j ≤ 32
  · exact chkR_spec _ _ _ _ _ c_4_5_0 j (by omega) (by omega)
  omega

theorem J_4_6 : J 4 6 = 64 ∧ J 4 6 * J 4 6 ≤ 4 ^ 6 ∧ 4 ^ 6 < (J 4 6 + 1) * (J 4 6 + 1) := by decide
theorem c_4_6_0 : chkR (4 ^ 6) 4 6 0 64 = true := by decide +kernel
theorem g_4_6 : ∀ j, 1 ≤ j → j ≤ J 4 6 → good (4 ^ 6) 4 6 j = true := by
  intro j h1 h2
  have hJ := J_4_6.1
  by_cases h0 : j ≤ 64
  · exact chkR_spec _ _ _ _ _ c_4_6_0 j (by omega) (by omega)
  omega

theorem J_4_7 : J 4 7 = 128 ∧ J 4 7 * J 4 7 ≤ 4 ^ 7 ∧ 4 ^ 7 < (J 4 7 + 1) * (J 4 7 + 1) := by decide
theorem c_4_7_0 : chkR (4 ^ 7) 4 7 0 128 = true := by decide +kernel
theorem g_4_7 : ∀ j, 1 ≤ j → j ≤ J 4 7 → good (4 ^ 7) 4 7 j = true := by
  intro j h1 h2
  have hJ := J_4_7.1
  by_cases h0 : j ≤ 128
  · exact chkR_spec _ _ _ _ _ c_4_7_0 j (by omega) (by omega)
  omega

theorem J_4_8 : J 4 8 = 256 ∧ J 4 8 * J 4 8 ≤ 4 ^ 8 ∧ 4 ^ 8 < (J 4 8 + 1) * (J 4 8 + 1) := by decide
theorem c_4_8_0 : chkR (4 ^ 8) 4 8 0 256 = true := by decide +kernel
theorem g_4_8 : ∀ j, 1 ≤ j → j ≤ J 4 8 → good (4 ^ 8) 4 8 j = true := by
  intro j h1 h2
  have hJ := J_4_8.1
  by_cases h0 : j ≤ 256
  · exact chkR_spec _ _ _ _ _ c_4_8_0 j (by omega) (by omega)
  omega

theorem J_4_9 : J 4 9 = 512 ∧ J 4 9 * J 4 9 ≤ 4 ^ 9 ∧ 4 ^ 9 < (J 4 9 + 1) * (J 4 9 + 1) := by decide
theorem c_4_9_0 : chkR (4 ^ 9) 4 9 0 512 = true := by decide +kernel
theorem g_4_9 : ∀ j, 1 ≤ j → j ≤ J 4 9 → good (4 ^ 9) 4 9 j = true := by
  intro j h1 h2
  have hJ := J_4_9.1
  by_cases h0 : j ≤ 512
  · exact chkR_spec _ _ _ _ _ c_4_9_0 j (by omega) (by omega)
  omega

theorem J_5_0 : J 5 0 = 1 ∧ J 5 0 * J 5 0 ≤ 5 ^ 0 ∧ 5 ^ 0 < (J 5 0 + 1) * (J 5 0 + 1) := by decide
theorem c_5_0_0 : chkR (5 ^ 0) 5 0 0 1 = true := by decide +kernel
theorem g_5_0 : ∀ j, 1 ≤ j → j ≤ J 5 0 → good (5 ^ 0) 5 0 j = true := by
  intro j h1 h2
  have hJ := J_5_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_5_0_0 j (by omega) (by omega)
  omega

theorem J_5_1 : J 5 1 = 2 ∧ J 5 1 * J 5 1 ≤ 5 ^ 1 ∧ 5 ^ 1 < (J 5 1 + 1) * (J 5 1 + 1) := by decide
theorem c_5_1_0 : chkR (5 ^ 1) 5 1 0 2 = true := by decide +kernel
theorem g_5_1 : ∀ j, 1 ≤ j → j ≤ J 5 1 → good (5 ^ 1) 5 1 j = true := by
  intro j h1 h2
  have hJ := J_5_1.1
  by_cases h0 : j ≤ 2
  · exact chkR_spec _ _ _ _ _ c_5_1_0 j (by omega) (by omega)
  omega

theorem J_5_2 : J 5 2 = 5 ∧ J 5 2 * J 5 2 ≤ 5 ^ 2 ∧ 5 ^ 2 < (J 5 2 + 1) * (J 5 2 + 1) := by decide
theorem c_5_2_0 : chkR (5 ^ 2) 5 2 0 5 = true := by decide +kernel
theorem g_5_2 : ∀ j, 1 ≤ j → j ≤ J 5 2 → good (5 ^ 2) 5 2 j = true := by
  intro j h1 h2
  have hJ := J_5_2.1
  by_cases h0 : j ≤ 5
  · exact chkR_spec _ _ _ _ _ c_5_2_0 j (by omega) (by omega)
  omega

theorem J_5_3 : J 5 3 = 11 ∧ J 5 3 * J 5 3 ≤ 5 ^ 3 ∧ 5 ^ 3 < (J 5 3 + 1) * (J 5 3 + 1) := by decide
theorem c_5_3_0 : chkR (5 ^ 3) 5 3 0 11 = true := by decide +kernel
theorem g_5_3 : ∀ j, 1 ≤ j → j ≤ J 5 3 → good (5 ^ 3) 5 3 j = true := by
  intro j h1 h2
  have hJ := J_5_3.1
  by_cases h0 : j ≤ 11
  · exact chkR_spec _ _ _ _ _ c_5_3_0 j (by omega) (by omega)
  omega

theorem J_5_4 : J 5 4 = 25 ∧ J 5 4 * J 5 4 ≤ 5 ^ 4 ∧ 5 ^ 4 < (J 5 4 + 1) * (J 5 4 + 1) := by decide
theorem c_5_4_0 : chkR (5 ^ 4) 5 4 0 25 = true := by decide +kernel
theorem g_5_4 : ∀ j, 1 ≤ j → j ≤ J 5 4 → good (5 ^ 4) 5 4 j = true := by
  intro j h1 h2
  have hJ := J_5_4.1
  by_cases h0 : j ≤ 25
  · exact chkR_spec _ _ _ _ _ c_5_4_0 j (by omega) (by omega)
  omega

theorem J_5_5 : J 5 5 = 55 ∧ J 5 5 * J 5 5 ≤ 5 ^ 5 ∧ 5 ^ 5 < (J 5 5 + 1) * (J 5 5 + 1) := by decide
theorem c_5_5_0 : chkR (5 ^ 5) 5 5 0 55 = true := by decide +kernel
theorem g_5_5 : ∀ j, 1 ≤ j → j ≤ J 5 5 → good (5 ^ 5) 5 5 j = true := by
  intro j h1 h2
  have hJ := J_5_5.1
  by_cases h0 : j ≤ 55
  · exact chkR_spec _ _ _ _ _ c_5_5_0 j (by omega) (by omega)
  omega

theorem J_5_6 : J 5 6 = 125 ∧ J 5 6 * J 5 6 ≤ 5 ^ 6 ∧ 5 ^ 6 < (J 5 6 + 1) * (J 5 6 + 1) := by decide
theorem c_5_6_0 : chkR (5 ^ 6) 5 6 0 125 = true := by decide +kernel
theorem g_5_6 : ∀ j, 1 ≤ j → j ≤ J 5 6 → good (5 ^ 6) 5 6 j = true := by
  intro j h1 h2
  have hJ := J_5_6.1
  by_cases h0 : j ≤ 125
  · exact chkR_spec _ _ _ _ _ c_5_6_0 j (by omega) (by omega)
  omega

theorem J_5_7 : J 5 7 = 279 ∧ J 5 7 * J 5 7 ≤ 5 ^ 7 ∧ 5 ^ 7 < (J 5 7 + 1) * (J 5 7 + 1) := by decide
theorem c_5_7_0 : chkR (5 ^ 7) 5 7 0 279 = true := by decide +kernel
theorem g_5_7 : ∀ j, 1 ≤ j → j ≤ J 5 7 → good (5 ^ 7) 5 7 j = true := by
  intro j h1 h2
  have hJ := J_5_7.1
  by_cases h0 : j ≤ 279
  · exact chkR_spec _ _ _ _ _ c_5_7_0 j (by omega) (by omega)
  omega

theorem J_5_8 : J 5 8 = 625 ∧ J 5 8 * J 5 8 ≤ 5 ^ 8 ∧ 5 ^ 8 < (J 5 8 + 1) * (J 5 8 + 1) := by decide
theorem c_5_8_0 : chkR (5 ^ 8) 5 8 0 625 = true := by decide +kernel
theorem g_5_8 : ∀ j, 1 ≤ j → j ≤ J 5 8 → good (5 ^ 8) 5 8 j = true := by
  intro j h1 h2
  have hJ := J_5_8.1
  by_cases h0 : j ≤ 625
  · exact chkR_spec _ _ _ _ _ c_5_8_0 j (by omega) (by omega)
  omega

theorem J_5_9 : J 5 9 = 1397 ∧ J 5 9 * J 5 9 ≤ 5 ^ 9 ∧ 5 ^ 9 < (J 5 9 + 1) * (J 5 9 + 1) := by decide
theorem c_5_9_0 : chkR (5 ^ 9) 5 9 0 1397 = true := by decide +kernel
theorem g_5_9 : ∀ j, 1 ≤ j → j ≤ J 5 9 → good (5 ^ 9) 5 9 j = true := by
  intro j h1 h2
  have hJ := J_5_9.1
  by_cases h0 : j ≤ 1397
  · exact chkR_spec _ _ _ _ _ c_5_9_0 j (by omega) (by omega)
  omega

theorem J_6_0 : J 6 0 = 1 ∧ J 6 0 * J 6 0 ≤ 6 ^ 0 ∧ 6 ^ 0 < (J 6 0 + 1) * (J 6 0 + 1) := by decide
theorem c_6_0_0 : chkR (6 ^ 0) 6 0 0 1 = true := by decide +kernel
theorem g_6_0 : ∀ j, 1 ≤ j → j ≤ J 6 0 → good (6 ^ 0) 6 0 j = true := by
  intro j h1 h2
  have hJ := J_6_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_6_0_0 j (by omega) (by omega)
  omega

theorem J_6_1 : J 6 1 = 2 ∧ J 6 1 * J 6 1 ≤ 6 ^ 1 ∧ 6 ^ 1 < (J 6 1 + 1) * (J 6 1 + 1) := by decide
theorem c_6_1_0 : chkR (6 ^ 1) 6 1 0 2 = true := by decide +kernel
theorem g_6_1 : ∀ j, 1 ≤ j → j ≤ J 6 1 → good (6 ^ 1) 6 1 j = true := by
  intro j h1 h2
  have hJ := J_6_1.1
  by_cases h0 : j ≤ 2
  · exact chkR_spec _ _ _ _ _ c_6_1_0 j (by omega) (by omega)
  omega

theorem J_6_2 : J 6 2 = 6 ∧ J 6 2 * J 6 2 ≤ 6 ^ 2 ∧ 6 ^ 2 < (J 6 2 + 1) * (J 6 2 + 1) := by decide
theorem c_6_2_0 : chkR (6 ^ 2) 6 2 0 6 = true := by decide +kernel
theorem g_6_2 : ∀ j, 1 ≤ j → j ≤ J 6 2 → good (6 ^ 2) 6 2 j = true := by
  intro j h1 h2
  have hJ := J_6_2.1
  by_cases h0 : j ≤ 6
  · exact chkR_spec _ _ _ _ _ c_6_2_0 j (by omega) (by omega)
  omega

theorem J_6_3 : J 6 3 = 14 ∧ J 6 3 * J 6 3 ≤ 6 ^ 3 ∧ 6 ^ 3 < (J 6 3 + 1) * (J 6 3 + 1) := by decide
theorem c_6_3_0 : chkR (6 ^ 3) 6 3 0 14 = true := by decide +kernel
theorem g_6_3 : ∀ j, 1 ≤ j → j ≤ J 6 3 → good (6 ^ 3) 6 3 j = true := by
  intro j h1 h2
  have hJ := J_6_3.1
  by_cases h0 : j ≤ 14
  · exact chkR_spec _ _ _ _ _ c_6_3_0 j (by omega) (by omega)
  omega

theorem J_6_4 : J 6 4 = 36 ∧ J 6 4 * J 6 4 ≤ 6 ^ 4 ∧ 6 ^ 4 < (J 6 4 + 1) * (J 6 4 + 1) := by decide
theorem c_6_4_0 : chkR (6 ^ 4) 6 4 0 36 = true := by decide +kernel
theorem g_6_4 : ∀ j, 1 ≤ j → j ≤ J 6 4 → good (6 ^ 4) 6 4 j = true := by
  intro j h1 h2
  have hJ := J_6_4.1
  by_cases h0 : j ≤ 36
  · exact chkR_spec _ _ _ _ _ c_6_4_0 j (by omega) (by omega)
  omega

theorem J_6_5 : J 6 5 = 88 ∧ J 6 5 * J 6 5 ≤ 6 ^ 5 ∧ 6 ^ 5 < (J 6 5 + 1) * (J 6 5 + 1) := by decide
theorem c_6_5_0 : chkR (6 ^ 5) 6 5 0 88 = true := by decide +kernel
theorem g_6_5 : ∀ j, 1 ≤ j → j ≤ J 6 5 → good (6 ^ 5) 6 5 j = true := by
  intro j h1 h2
  have hJ := J_6_5.1
  by_cases h0 : j ≤ 88
  · exact chkR_spec _ _ _ _ _ c_6_5_0 j (by omega) (by omega)
  omega

theorem J_6_6 : J 6 6 = 216 ∧ J 6 6 * J 6 6 ≤ 6 ^ 6 ∧ 6 ^ 6 < (J 6 6 + 1) * (J 6 6 + 1) := by decide
theorem c_6_6_0 : chkR (6 ^ 6) 6 6 0 216 = true := by decide +kernel
theorem g_6_6 : ∀ j, 1 ≤ j → j ≤ J 6 6 → good (6 ^ 6) 6 6 j = true := by
  intro j h1 h2
  have hJ := J_6_6.1
  by_cases h0 : j ≤ 216
  · exact chkR_spec _ _ _ _ _ c_6_6_0 j (by omega) (by omega)
  omega

theorem J_6_7 : J 6 7 = 529 ∧ J 6 7 * J 6 7 ≤ 6 ^ 7 ∧ 6 ^ 7 < (J 6 7 + 1) * (J 6 7 + 1) := by decide
theorem c_6_7_0 : chkR (6 ^ 7) 6 7 0 529 = true := by decide +kernel
theorem g_6_7 : ∀ j, 1 ≤ j → j ≤ J 6 7 → good (6 ^ 7) 6 7 j = true := by
  intro j h1 h2
  have hJ := J_6_7.1
  by_cases h0 : j ≤ 529
  · exact chkR_spec _ _ _ _ _ c_6_7_0 j (by omega) (by omega)
  omega

theorem J_6_8 : J 6 8 = 1296 ∧ J 6 8 * J 6 8 ≤ 6 ^ 8 ∧ 6 ^ 8 < (J 6 8 + 1) * (J 6 8 + 1) := by decide
theorem c_6_8_0 : chkR (6 ^ 8) 6 8 0 1296 = true := by decide +kernel
theorem g_6_8 : ∀ j, 1 ≤ j → j ≤ J 6 8 → good (6 ^ 8) 6 8 j = true := by
  intro j h1 h2
  have hJ := J_6_8.1
  by_cases h0 : j ≤ 1296
  · exact chkR_spec _ _ _ _ _ c_6_8_0 j (by omega) (by omega)
  omega

theorem J_6_9 : J 6 9 = 3174 ∧ J 6 9 * J 6 9 ≤ 6 ^ 9 ∧ 6 ^ 9 < (J 6 9 + 1) * (J 6 9 + 1) := by decide
theorem c_6_9_0 : chkR (6 ^ 9) 6 9 0 3174 = true := by decide +kernel
theorem g_6_9 : ∀ j, 1 ≤ j → j ≤ J 6 9 → good (6 ^ 9) 6 9 j = true := by
  intro j h1 h2
  have hJ := J_6_9.1
  by_cases h0 : j ≤ 3174
  · exact chkR_spec _ _ _ _ _ c_6_9_0 j (by omega) (by omega)
  omega

theorem J_7_0 : J 7 0 = 1 ∧ J 7 0 * J 7 0 ≤ 7 ^ 0 ∧ 7 ^ 0 < (J 7 0 + 1) * (J 7 0 + 1) := by decide
theorem c_7_0_0 : chkR (7 ^ 0) 7 0 0 1 = true := by decide +kernel
theorem g_7_0 : ∀ j, 1 ≤ j → j ≤ J 7 0 → good (7 ^ 0) 7 0 j = true := by
  intro j h1 h2
  have hJ := J_7_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_7_0_0 j (by omega) (by omega)
  omega

theorem J_7_1 : J 7 1 = 2 ∧ J 7 1 * J 7 1 ≤ 7 ^ 1 ∧ 7 ^ 1 < (J 7 1 + 1) * (J 7 1 + 1) := by decide
theorem c_7_1_0 : chkR (7 ^ 1) 7 1 0 2 = true := by decide +kernel
theorem g_7_1 : ∀ j, 1 ≤ j → j ≤ J 7 1 → good (7 ^ 1) 7 1 j = true := by
  intro j h1 h2
  have hJ := J_7_1.1
  by_cases h0 : j ≤ 2
  · exact chkR_spec _ _ _ _ _ c_7_1_0 j (by omega) (by omega)
  omega

theorem J_7_2 : J 7 2 = 7 ∧ J 7 2 * J 7 2 ≤ 7 ^ 2 ∧ 7 ^ 2 < (J 7 2 + 1) * (J 7 2 + 1) := by decide
theorem c_7_2_0 : chkR (7 ^ 2) 7 2 0 7 = true := by decide +kernel
theorem g_7_2 : ∀ j, 1 ≤ j → j ≤ J 7 2 → good (7 ^ 2) 7 2 j = true := by
  intro j h1 h2
  have hJ := J_7_2.1
  by_cases h0 : j ≤ 7
  · exact chkR_spec _ _ _ _ _ c_7_2_0 j (by omega) (by omega)
  omega

theorem J_7_3 : J 7 3 = 18 ∧ J 7 3 * J 7 3 ≤ 7 ^ 3 ∧ 7 ^ 3 < (J 7 3 + 1) * (J 7 3 + 1) := by decide
theorem c_7_3_0 : chkR (7 ^ 3) 7 3 0 18 = true := by decide +kernel
theorem g_7_3 : ∀ j, 1 ≤ j → j ≤ J 7 3 → good (7 ^ 3) 7 3 j = true := by
  intro j h1 h2
  have hJ := J_7_3.1
  by_cases h0 : j ≤ 18
  · exact chkR_spec _ _ _ _ _ c_7_3_0 j (by omega) (by omega)
  omega

theorem J_7_4 : J 7 4 = 49 ∧ J 7 4 * J 7 4 ≤ 7 ^ 4 ∧ 7 ^ 4 < (J 7 4 + 1) * (J 7 4 + 1) := by decide
theorem c_7_4_0 : chkR (7 ^ 4) 7 4 0 49 = true := by decide +kernel
theorem g_7_4 : ∀ j, 1 ≤ j → j ≤ J 7 4 → good (7 ^ 4) 7 4 j = true := by
  intro j h1 h2
  have hJ := J_7_4.1
  by_cases h0 : j ≤ 49
  · exact chkR_spec _ _ _ _ _ c_7_4_0 j (by omega) (by omega)
  omega

theorem J_7_5 : J 7 5 = 129 ∧ J 7 5 * J 7 5 ≤ 7 ^ 5 ∧ 7 ^ 5 < (J 7 5 + 1) * (J 7 5 + 1) := by decide
theorem c_7_5_0 : chkR (7 ^ 5) 7 5 0 129 = true := by decide +kernel
theorem g_7_5 : ∀ j, 1 ≤ j → j ≤ J 7 5 → good (7 ^ 5) 7 5 j = true := by
  intro j h1 h2
  have hJ := J_7_5.1
  by_cases h0 : j ≤ 129
  · exact chkR_spec _ _ _ _ _ c_7_5_0 j (by omega) (by omega)
  omega

theorem J_7_6 : J 7 6 = 343 ∧ J 7 6 * J 7 6 ≤ 7 ^ 6 ∧ 7 ^ 6 < (J 7 6 + 1) * (J 7 6 + 1) := by decide
theorem c_7_6_0 : chkR (7 ^ 6) 7 6 0 343 = true := by decide +kernel
theorem g_7_6 : ∀ j, 1 ≤ j → j ≤ J 7 6 → good (7 ^ 6) 7 6 j = true := by
  intro j h1 h2
  have hJ := J_7_6.1
  by_cases h0 : j ≤ 343
  · exact chkR_spec _ _ _ _ _ c_7_6_0 j (by omega) (by omega)
  omega

theorem J_7_7 : J 7 7 = 907 ∧ J 7 7 * J 7 7 ≤ 7 ^ 7 ∧ 7 ^ 7 < (J 7 7 + 1) * (J 7 7 + 1) := by decide
theorem c_7_7_0 : chkR (7 ^ 7) 7 7 0 907 = true := by decide +kernel
theorem g_7_7 : ∀ j, 1 ≤ j → j ≤ J 7 7 → good (7 ^ 7) 7 7 j = true := by
  intro j h1 h2
  have hJ := J_7_7.1
  by_cases h0 : j ≤ 907
  · exact chkR_spec _ _ _ _ _ c_7_7_0 j (by omega) (by omega)
  omega

theorem J_7_8 : J 7 8 = 2401 ∧ J 7 8 * J 7 8 ≤ 7 ^ 8 ∧ 7 ^ 8 < (J 7 8 + 1) * (J 7 8 + 1) := by decide
theorem c_7_8_0 : chkR (7 ^ 8) 7 8 0 2401 = true := by decide +kernel
theorem g_7_8 : ∀ j, 1 ≤ j → j ≤ J 7 8 → good (7 ^ 8) 7 8 j = true := by
  intro j h1 h2
  have hJ := J_7_8.1
  by_cases h0 : j ≤ 2401
  · exact chkR_spec _ _ _ _ _ c_7_8_0 j (by omega) (by omega)
  omega

theorem J_7_9 : J 7 9 = 6352 ∧ J 7 9 * J 7 9 ≤ 7 ^ 9 ∧ 7 ^ 9 < (J 7 9 + 1) * (J 7 9 + 1) := by decide
theorem c_7_9_0 : chkR (7 ^ 9) 7 9 0 5000 = true := by decide +kernel
theorem c_7_9_5000 : chkR (7 ^ 9) 7 9 5000 1352 = true := by decide +kernel
theorem g_7_9 : ∀ j, 1 ≤ j → j ≤ J 7 9 → good (7 ^ 9) 7 9 j = true := by
  intro j h1 h2
  have hJ := J_7_9.1
  by_cases h0 : j ≤ 5000
  · exact chkR_spec _ _ _ _ _ c_7_9_0 j (by omega) (by omega)
  by_cases h1 : j ≤ 6352
  · exact chkR_spec _ _ _ _ _ c_7_9_5000 j (by omega) (by omega)
  omega

theorem J_8_0 : J 8 0 = 1 ∧ J 8 0 * J 8 0 ≤ 8 ^ 0 ∧ 8 ^ 0 < (J 8 0 + 1) * (J 8 0 + 1) := by decide
theorem c_8_0_0 : chkR (8 ^ 0) 8 0 0 1 = true := by decide +kernel
theorem g_8_0 : ∀ j, 1 ≤ j → j ≤ J 8 0 → good (8 ^ 0) 8 0 j = true := by
  intro j h1 h2
  have hJ := J_8_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_8_0_0 j (by omega) (by omega)
  omega

theorem J_8_1 : J 8 1 = 2 ∧ J 8 1 * J 8 1 ≤ 8 ^ 1 ∧ 8 ^ 1 < (J 8 1 + 1) * (J 8 1 + 1) := by decide
theorem c_8_1_0 : chkR (8 ^ 1) 8 1 0 2 = true := by decide +kernel
theorem g_8_1 : ∀ j, 1 ≤ j → j ≤ J 8 1 → good (8 ^ 1) 8 1 j = true := by
  intro j h1 h2
  have hJ := J_8_1.1
  by_cases h0 : j ≤ 2
  · exact chkR_spec _ _ _ _ _ c_8_1_0 j (by omega) (by omega)
  omega

theorem J_8_2 : J 8 2 = 8 ∧ J 8 2 * J 8 2 ≤ 8 ^ 2 ∧ 8 ^ 2 < (J 8 2 + 1) * (J 8 2 + 1) := by decide
theorem c_8_2_0 : chkR (8 ^ 2) 8 2 0 8 = true := by decide +kernel
theorem g_8_2 : ∀ j, 1 ≤ j → j ≤ J 8 2 → good (8 ^ 2) 8 2 j = true := by
  intro j h1 h2
  have hJ := J_8_2.1
  by_cases h0 : j ≤ 8
  · exact chkR_spec _ _ _ _ _ c_8_2_0 j (by omega) (by omega)
  omega

theorem J_8_3 : J 8 3 = 22 ∧ J 8 3 * J 8 3 ≤ 8 ^ 3 ∧ 8 ^ 3 < (J 8 3 + 1) * (J 8 3 + 1) := by decide
theorem c_8_3_0 : chkR (8 ^ 3) 8 3 0 22 = true := by decide +kernel
theorem g_8_3 : ∀ j, 1 ≤ j → j ≤ J 8 3 → good (8 ^ 3) 8 3 j = true := by
  intro j h1 h2
  have hJ := J_8_3.1
  by_cases h0 : j ≤ 22
  · exact chkR_spec _ _ _ _ _ c_8_3_0 j (by omega) (by omega)
  omega

theorem J_8_4 : J 8 4 = 64 ∧ J 8 4 * J 8 4 ≤ 8 ^ 4 ∧ 8 ^ 4 < (J 8 4 + 1) * (J 8 4 + 1) := by decide
theorem c_8_4_0 : chkR (8 ^ 4) 8 4 0 64 = true := by decide +kernel
theorem g_8_4 : ∀ j, 1 ≤ j → j ≤ J 8 4 → good (8 ^ 4) 8 4 j = true := by
  intro j h1 h2
  have hJ := J_8_4.1
  by_cases h0 : j ≤ 64
  · exact chkR_spec _ _ _ _ _ c_8_4_0 j (by omega) (by omega)
  omega

theorem J_8_5 : J 8 5 = 181 ∧ J 8 5 * J 8 5 ≤ 8 ^ 5 ∧ 8 ^ 5 < (J 8 5 + 1) * (J 8 5 + 1) := by decide
theorem c_8_5_0 : chkR (8 ^ 5) 8 5 0 181 = true := by decide +kernel
theorem g_8_5 : ∀ j, 1 ≤ j → j ≤ J 8 5 → good (8 ^ 5) 8 5 j = true := by
  intro j h1 h2
  have hJ := J_8_5.1
  by_cases h0 : j ≤ 181
  · exact chkR_spec _ _ _ _ _ c_8_5_0 j (by omega) (by omega)
  omega

theorem J_8_6 : J 8 6 = 512 ∧ J 8 6 * J 8 6 ≤ 8 ^ 6 ∧ 8 ^ 6 < (J 8 6 + 1) * (J 8 6 + 1) := by decide
theorem c_8_6_0 : chkR (8 ^ 6) 8 6 0 512 = true := by decide +kernel
theorem g_8_6 : ∀ j, 1 ≤ j → j ≤ J 8 6 → good (8 ^ 6) 8 6 j = true := by
  intro j h1 h2
  have hJ := J_8_6.1
  by_cases h0 : j ≤ 512
  · exact chkR_spec _ _ _ _ _ c_8_6_0 j (by omega) (by omega)
  omega

theorem J_8_7 : J 8 7 = 1448 ∧ J 8 7 * J 8 7 ≤ 8 ^ 7 ∧ 8 ^ 7 < (J 8 7 + 1) * (J 8 7 + 1) := by decide
theorem c_8_7_0 : chkR (8 ^ 7) 8 7 0 1448 = true := by decide +kernel
theorem g_8_7 : ∀ j, 1 ≤ j → j ≤ J 8 7 → good (8 ^ 7) 8 7 j = true := by
  intro j h1 h2
  have hJ := J_8_7.1
  by_cases h0 : j ≤ 1448
  · exact chkR_spec _ _ _ _ _ c_8_7_0 j (by omega) (by omega)
  omega

theorem J_8_8 : J 8 8 = 4096 ∧ J 8 8 * J 8 8 ≤ 8 ^ 8 ∧ 8 ^ 8 < (J 8 8 + 1) * (J 8 8 + 1) := by decide
theorem c_8_8_0 : chkR (8 ^ 8) 8 8 0 4096 = true := by decide +kernel
theorem g_8_8 : ∀ j, 1 ≤ j → j ≤ J 8 8 → good (8 ^ 8) 8 8 j = true := by
  intro j h1 h2
  have hJ := J_8_8.1
  by_cases h0 : j ≤ 4096
  · exact chkR_spec _ _ _ _ _ c_8_8_0 j (by omega) (by omega)
  omega

theorem J_8_9 : J 8 9 = 11585 ∧ J 8 9 * J 8 9 ≤ 8 ^ 9 ∧ 8 ^ 9 < (J 8 9 + 1) * (J 8 9 + 1) := by decide
theorem c_8_9_0 : chkR (8 ^ 9) 8 9 0 5000 = true := by decide +kernel
theorem c_8_9_5000 : chkR (8 ^ 9) 8 9 5000 5000 = true := by decide +kernel
theorem c_8_9_10000 : chkR (8 ^ 9) 8 9 10000 1585 = true := by decide +kernel
theorem g_8_9 : ∀ j, 1 ≤ j → j ≤ J 8 9 → good (8 ^ 9) 8 9 j = true := by
  intro j h1 h2
  have hJ := J_8_9.1
  by_cases h0 : j ≤ 5000
  · exact chkR_spec _ _ _ _ _ c_8_9_0 j (by omega) (by omega)
  by_cases h1 : j ≤ 10000
  · exact chkR_spec _ _ _ _ _ c_8_9_5000 j (by omega) (by omega)
  by_cases h2 : j ≤ 11585
  · exact chkR_spec _ _ _ _ _ c_8_9_10000 j (by omega) (by omega)
  omega

theorem J_9_0 : J 9 0 = 1 ∧ J 9 0 * J 9 0 ≤ 9 ^ 0 ∧ 9 ^ 0 < (J 9 0 + 1) * (J 9 0 + 1) := by decide
theorem c_9_0_0 : chkR (9 ^ 0) 9 0 0 1 = true := by decide +kernel
theorem g_9_0 : ∀ j, 1 ≤ j → j ≤ J 9 0 → good (9 ^ 0) 9 0 j = true := by
  intro j h1 h2
  have hJ := J_9_0.1
  by_cases h0 : j ≤ 1
  · exact chkR_spec _ _ _ _ _ c_9_0_0 j (by omega) (by omega)
  omega

theorem J_9_1 : J 9 1 = 3 ∧ J 9 1 * J 9 1 ≤ 9 ^ 1 ∧ 9 ^ 1 < (J 9 1 + 1) * (J 9 1 + 1) := by decide
theorem c_9_1_0 : chkR (9 ^ 1) 9 1 0 3 = true := by decide +kernel
theorem g_9_1 : ∀ j, 1 ≤ j → j ≤ J 9 1 → good (9 ^ 1) 9 1 j = true := by
  intro j h1 h2
  have hJ := J_9_1.1
  by_cases h0 : j ≤ 3
  · exact chkR_spec _ _ _ _ _ c_9_1_0 j (by omega) (by omega)
  omega

theorem J_9_2 : J 9 2 = 9 ∧ J 9 2 * J 9 2 ≤ 9 ^ 2 ∧ 9 ^ 2 < (J 9 2 + 1) * (J 9 2 + 1) := by decide
theorem c_9_2_0 : chkR (9 ^ 2) 9 2 0 9 = true := by decide +kernel
theorem g_9_2 : ∀ j, 1 ≤ j → j ≤ J 9 2 → good (9 ^ 2) 9 2 j = true := by
  intro j h1 h2
  have hJ := J_9_2.1
  by_cases h0 : j ≤ 9
  · exact chkR_spec _ _ _ _ _ c_9_2_0 j (by omega) (by omega)
  omega

theorem J_9_3 : J 9 3 = 27 ∧ J 9 3 * J 9 3 ≤ 9 ^ 3 ∧ 9 ^ 3 < (J 9 3 + 1) * (J 9 3 + 1) := by decide
theorem c_9_3_0 : chkR (9 ^ 3) 9 3 0 27 = true := by decide +kernel
theorem g_9_3 : ∀ j, 1 ≤ j → j ≤ J 9 3 → good (9 ^ 3) 9 3 j = true := by
  intro j h1 h2
  have hJ := J_9_3.1
  by_cases h0 : j ≤ 27
  · exact chkR_spec _ _ _ _ _ c_9_3_0 j (by omega) (by omega)
  omega

theorem J_9_4 : J 9 4 = 81 ∧ J 9 4 * J 9 4 ≤ 9 ^ 4 ∧ 9 ^ 4 < (J 9 4 + 1) * (J 9 4 + 1) := by decide
theorem c_9_4_0 : chkR (9 ^ 4) 9 4 0 81 = true := by decide +kernel
theorem g_9_4 : ∀ j, 1 ≤ j → j ≤ J 9 4 → good (9 ^ 4) 9 4 j = true := by
  intro j h1 h2
  have hJ := J_9_4.1
  by_cases h0 : j ≤ 81
  · exact chkR_spec _ _ _ _ _ c_9_4_0 j (by omega) (by omega)
  omega

theorem J_9_5 : J 9 5 = 243 ∧ J 9 5 * J 9 5 ≤ 9 ^ 5 ∧ 9 ^ 5 < (J 9 5 + 1) * (J 9 5 + 1) := by decide
theorem c_9_5_0 : chkR (9 ^ 5) 9 5 0 243 = true := by decide +kernel
theorem g_9_5 : ∀ j, 1 ≤ j → j ≤ J 9 5 → good (9 ^ 5) 9 5 j = true := by
  intro j h1 h2
  have hJ := J_9_5.1
  by_cases h0 : j ≤ 243
  · exact chkR_spec _ _ _ _ _ c_9_5_0 j (by omega) (by omega)
  omega

theorem J_9_6 : J 9 6 = 729 ∧ J 9 6 * J 9 6 ≤ 9 ^ 6 ∧ 9 ^ 6 < (J 9 6 + 1) * (J 9 6 + 1) := by decide
theorem c_9_6_0 : chkR (9 ^ 6) 9 6 0 729 = true := by decide +kernel
theorem g_9_6 : ∀ j, 1 ≤ j → j ≤ J 9 6 → good (9 ^ 6) 9 6 j = true := by
  intro j h1 h2
  have hJ := J_9_6.1
  by_cases h0 : j ≤ 729
  · exact chkR_spec _ _ _ _ _ c_9_6_0 j (by omega) (by omega)
  omega

theorem J_9_7 : J 9 7 = 2187 ∧ J 9 7 * J 9 7 ≤ 9 ^ 7 ∧ 9 ^ 7 < (J 9 7 + 1) * (J 9 7 + 1) := by decide
theorem c_9_7_0 : chkR (9 ^ 7) 9 7 0 2187 = true := by decide +kernel
theorem g_9_7 : ∀ j, 1 ≤ j → j ≤ J 9 7 → good (9 ^ 7) 9 7 j = true := by
  intro j h1 h2
  have hJ := J_9_7.1
  by_cases h0 : j ≤ 2187
  · exact chkR_spec _ _ _ _ _ c_9_7_0 j (by omega) (by omega)
  omega

theorem J_9_8 : J 9 8 = 6561 ∧ J 9 8 * J 9 8 ≤ 9 ^ 8 ∧ 9 ^ 8 < (J 9 8 + 1) * (J 9 8 + 1) := by decide
theorem c_9_8_0 : chkR (9 ^ 8) 9 8 0 5000 = true := by decide +kernel
theorem c_9_8_5000 : chkR (9 ^ 8) 9 8 5000 1561 = true := by decide +kernel
theorem g_9_8 : ∀ j, 1 ≤ j → j ≤ J 9 8 → good (9 ^ 8) 9 8 j = true := by
  intro j h1 h2
  have hJ := J_9_8.1
  by_cases h0 : j ≤ 5000
  · exact chkR_spec _ _ _ _ _ c_9_8_0 j (by omega) (by omega)
  by_cases h1 : j ≤ 6561
  · exact chkR_spec _ _ _ _ _ c_9_8_5000 j (by omega) (by omega)
  omega

theorem J_9_9 : J 9 9 = 19683 ∧ J 9 9 * J 9 9 ≤ 9 ^ 9 ∧ 9 ^ 9 < (J 9 9 + 1) * (J 9 9 + 1) := by decide
theorem c_9_9_0 : chkR (9 ^ 9) 9 9 0 5000 = true := by decide +kernel
theorem c_9_9_5000 : chkR (9 ^ 9) 9 9 5000 5000 = true := by decide +kernel
theorem c_9_9_10000 : chkR (9 ^ 9) 9 9 10000 5000 = true := by decide +kernel
theorem c_9_9_15000 : chkR (9 ^ 9) 9 9 15000 4683 = true := by decide +kernel
theorem g_9_9 : ∀ j, 1 ≤ j → j ≤ J 9 9 → good (9 ^ 9) 9 9 j = true := by
  intro j h1 h2
  have hJ := J_9_9.1
  by_cases h0 : j ≤ 5000
  · exact chkR_spec _ _ _ _ _ c_9_9_0 j (by omega) (by omega)
  by_cases h1 : j ≤ 10000
  · exact chkR_spec _ _ _ _ _ c_9_9_5000 j (by omega) (by omega)
  by_cases h2 : j ≤ 15000
  · exact chkR_spec _ _ _ _ _ c_9_9_10000 j (by omega) (by omega)
  by_cases h3 : j ≤ 19683
  · exact chkR_spec _ _ _ _ _ c_9_9_15000 j (by omega) (by omega)
  omega

theorem allgood : ∀ a b, a < 10 → b < 10 → (J a b * J a b ≤ a ^ b ∧ a ^ b < (J a b + 1) * (J a b + 1)) ∧
    ∀ j, 1 ≤ j → j ≤ J a b → good (a ^ b) a b j = true
  | 0, 0, _, _ => ⟨J_0_0.2, g_0_0⟩
  | 0, 1, _, _ => ⟨J_0_1.2, g_0_1⟩
  | 0, 2, _, _ => ⟨J_0_2.2, g_0_2⟩
  | 0, 3, _, _ => ⟨J_0_3.2, g_0_3⟩
  | 0, 4, _, _ => ⟨J_0_4.2, g_0_4⟩
  | 0, 5, _, _ => ⟨J_0_5.2, g_0_5⟩
  | 0, 6, _, _ => ⟨J_0_6.2, g_0_6⟩
  | 0, 7, _, _ => ⟨J_0_7.2, g_0_7⟩
  | 0, 8, _, _ => ⟨J_0_8.2, g_0_8⟩
  | 0, 9, _, _ => ⟨J_0_9.2, g_0_9⟩
  | 1, 0, _, _ => ⟨J_1_0.2, g_1_0⟩
  | 1, 1, _, _ => ⟨J_1_1.2, g_1_1⟩
  | 1, 2, _, _ => ⟨J_1_2.2, g_1_2⟩
  | 1, 3, _, _ => ⟨J_1_3.2, g_1_3⟩
  | 1, 4, _, _ => ⟨J_1_4.2, g_1_4⟩
  | 1, 5, _, _ => ⟨J_1_5.2, g_1_5⟩
  | 1, 6, _, _ => ⟨J_1_6.2, g_1_6⟩
  | 1, 7, _, _ => ⟨J_1_7.2, g_1_7⟩
  | 1, 8, _, _ => ⟨J_1_8.2, g_1_8⟩
  | 1, 9, _, _ => ⟨J_1_9.2, g_1_9⟩
  | 2, 0, _, _ => ⟨J_2_0.2, g_2_0⟩
  | 2, 1, _, _ => ⟨J_2_1.2, g_2_1⟩
  | 2, 2, _, _ => ⟨J_2_2.2, g_2_2⟩
  | 2, 3, _, _ => ⟨J_2_3.2, g_2_3⟩
  | 2, 4, _, _ => ⟨J_2_4.2, g_2_4⟩
  | 2, 5, _, _ => ⟨J_2_5.2, g_2_5⟩
  | 2, 6, _, _ => ⟨J_2_6.2, g_2_6⟩
  | 2, 7, _, _ => ⟨J_2_7.2, g_2_7⟩
  | 2, 8, _, _ => ⟨J_2_8.2, g_2_8⟩
  | 2, 9, _, _ => ⟨J_2_9.2, g_2_9⟩
  | 3, 0, _, _ => ⟨J_3_0.2, g_3_0⟩
  | 3, 1, _, _ => ⟨J_3_1.2, g_3_1⟩
  | 3, 2, _, _ => ⟨J_3_2.2, g_3_2⟩
  | 3, 3, _, _ => ⟨J_3_3.2, g_3_3⟩
  | 3, 4, _, _ => ⟨J_3_4.2, g_3_4⟩
  | 3, 5, _, _ => ⟨J_3_5.2, g_3_5⟩
  | 3, 6, _, _ => ⟨J_3_6.2, g_3_6⟩
  | 3, 7, _, _ => ⟨J_3_7.2, g_3_7⟩
  | 3, 8, _, _ => ⟨J_3_8.2, g_3_8⟩
  | 3, 9, _, _ => ⟨J_3_9.2, g_3_9⟩
  | 4, 0, _, _ => ⟨J_4_0.2, g_4_0⟩
  | 4, 1, _, _ => ⟨J_4_1.2, g_4_1⟩
  | 4, 2, _, _ => ⟨J_4_2.2, g_4_2⟩
  | 4, 3, _, _ => ⟨J_4_3.2, g_4_3⟩
  | 4, 4, _, _ => ⟨J_4_4.2, g_4_4⟩
  | 4, 5, _, _ => ⟨J_4_5.2, g_4_5⟩
  | 4, 6, _, _ => ⟨J_4_6.2, g_4_6⟩
  | 4, 7, _, _ => ⟨J_4_7.2, g_4_7⟩
  | 4, 8, _, _ => ⟨J_4_8.2, g_4_8⟩
  | 4, 9, _, _ => ⟨J_4_9.2, g_4_9⟩
  | 5, 0, _, _ => ⟨J_5_0.2, g_5_0⟩
  | 5, 1, _, _ => ⟨J_5_1.2, g_5_1⟩
  | 5, 2, _, _ => ⟨J_5_2.2, g_5_2⟩
  | 5, 3, _, _ => ⟨J_5_3.2, g_5_3⟩
  | 5, 4, _, _ => ⟨J_5_4.2, g_5_4⟩
  | 5, 5, _, _ => ⟨J_5_5.2, g_5_5⟩
  | 5, 6, _, _ => ⟨J_5_6.2, g_5_6⟩
  | 5, 7, _, _ => ⟨J_5_7.2, g_5_7⟩
  | 5, 8, _, _ => ⟨J_5_8.2, g_5_8⟩
  | 5, 9, _, _ => ⟨J_5_9.2, g_5_9⟩
  | 6, 0, _, _ => ⟨J_6_0.2, g_6_0⟩
  | 6, 1, _, _ => ⟨J_6_1.2, g_6_1⟩
  | 6, 2, _, _ => ⟨J_6_2.2, g_6_2⟩
  | 6, 3, _, _ => ⟨J_6_3.2, g_6_3⟩
  | 6, 4, _, _ => ⟨J_6_4.2, g_6_4⟩
  | 6, 5, _, _ => ⟨J_6_5.2, g_6_5⟩
  | 6, 6, _, _ => ⟨J_6_6.2, g_6_6⟩
  | 6, 7, _, _ => ⟨J_6_7.2, g_6_7⟩
  | 6, 8, _, _ => ⟨J_6_8.2, g_6_8⟩
  | 6, 9, _, _ => ⟨J_6_9.2, g_6_9⟩
  | 7, 0, _, _ => ⟨J_7_0.2, g_7_0⟩
  | 7, 1, _, _ => ⟨J_7_1.2, g_7_1⟩
  | 7, 2, _, _ => ⟨J_7_2.2, g_7_2⟩
  | 7, 3, _, _ => ⟨J_7_3.2, g_7_3⟩
  | 7, 4, _, _ => ⟨J_7_4.2, g_7_4⟩
  | 7, 5, _, _ => ⟨J_7_5.2, g_7_5⟩
  | 7, 6, _, _ => ⟨J_7_6.2, g_7_6⟩
  | 7, 7, _, _ => ⟨J_7_7.2, g_7_7⟩
  | 7, 8, _, _ => ⟨J_7_8.2, g_7_8⟩
  | 7, 9, _, _ => ⟨J_7_9.2, g_7_9⟩
  | 8, 0, _, _ => ⟨J_8_0.2, g_8_0⟩
  | 8, 1, _, _ => ⟨J_8_1.2, g_8_1⟩
  | 8, 2, _, _ => ⟨J_8_2.2, g_8_2⟩
  | 8, 3, _, _ => ⟨J_8_3.2, g_8_3⟩
  | 8, 4, _, _ => ⟨J_8_4.2, g_8_4⟩
  | 8, 5, _, _ => ⟨J_8_5.2, g_8_5⟩
  | 8, 6, _, _ => ⟨J_8_6.2, g_8_6⟩
  | 8, 7, _, _ => ⟨J_8_7.2, g_8_7⟩
  | 8, 8, _, _ => ⟨J_8_8.2, g_8_8⟩
  | 8, 9, _, _ => ⟨J_8_9.2, g_8_9⟩
  | 9, 0, _, _ => ⟨J_9_0.2, g_9_0⟩
  | 9, 1, _, _ => ⟨J_9_1.2, g_9_1⟩
  | 9, 2, _, _ => ⟨J_9_2.2, g_9_2⟩
  | 9, 3, _, _ => ⟨J_9_3.2, g_9_3⟩
  | 9, 4, _, _ => ⟨J_9_4.2, g_9_4⟩
  | 9, 5, _, _ => ⟨J_9_5.2, g_9_5⟩
  | 9, 6, _, _ => ⟨J_9_6.2, g_9_6⟩
  | 9, 7, _, _ => ⟨J_9_7.2, g_9_7⟩
  | 9, 8, _, _ => ⟨J_9_8.2, g_9_8⟩
  | 9, 9, _, _ => ⟨J_9_9.2, g_9_9⟩
  | _ + 10, _, h, _ => absurd h (by omega)
  | _, _ + 10, _, h => absurd h (by omega)

theorem foldl_max_le (l : List Nat) : ∀ acc, acc ≤ 9 → (∀ x ∈ l, x ≤ 9) →
    l.foldl max acc ≤ 9 := by
  induction l with
  | nil => intro acc h _; simpa using h
  | cons y l ih =>
    intro acc h hl
    simp only [List.foldl]
    apply ih
    · have := hl y (by simp); omega
    · intro x hx; exact hl x (by simp [hx])

theorem le_foldl_max (l : List Nat) : ∀ acc x, (x ∈ l ∨ x ≤ acc) → x ≤ l.foldl max acc := by
  induction l with
  | nil => intro acc x h; simp at h; simpa using h
  | cons y l ih =>
    intro acc x h
    simp only [List.foldl]
    apply ih
    simp at h
    rcases h with (h | h) | h
    · right; subst h; omega
    · left; exact h
    · right; omega

theorem foldl_min_le (l : List Nat) : ∀ acc, l.foldl min acc ≤ acc := by
  induction l with
  | nil => intro acc; simp
  | cons y l ih =>
    intro acc
    simp only [List.foldl]
    have := ih (min acc y); omega

theorem digsF_le (f : Nat) : ∀ n, ∀ x ∈ digsF f n, x ≤ 9 := by
  induction f with
  | zero => intro n x hx; simp [digsF] at hx; omega
  | succ f ih =>
    intro n x hx
    simp only [digsF] at hx
    split at hx
    · simp at hx; omega
    · simp at hx
      rcases hx with h | h
      · omega
      · exact ih _ _ h

theorem digsF_ne (f : Nat) : ∀ n, n < f → n ≠ 0 → ∃ x ∈ digsF f n, x ≠ 0 := by
  induction f with
  | zero => intro n h; omega
  | succ f ih =>
    intro n h hn
    simp only [digsF]
    split
    · exact ⟨n, by simp, hn⟩
    · obtain ⟨x, hx, hx0⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨x, by simp [hx], hx0⟩

theorem maxD_le (n : Nat) : maxD n ≤ 9 :=
  foldl_max_le _ 0 (by omega) (digsF_le _ _)

theorem minD_le (n : Nat) : minD n ≤ 9 := foldl_min_le _ 9

theorem maxD_zero (n : Nat) (h : maxD n = 0) : n = 0 := by
  by_cases hn : n = 0
  · exact hn
  · obtain ⟨x, hx, hx0⟩ := digsF_ne (n + 1) n (by omega) hn
    have := le_foldl_max (digs n) 0 x (Or.inl hx)
    unfold maxD at h; omega

theorem A096913_squares (s t : Nat) (h : s * s + maxD (s * s) ^ minD (s * s) = t * t) :
    s * s = 0 ∨ s * s = 3844 := by
  generalize ha : maxD (s * s) = a at h
  generalize hb : minD (s * s) = b at h
  have ha9 : a ≤ 9 := ha ▸ maxD_le _
  have hb9 : b ≤ 9 := hb ▸ minD_le _
  by_cases ha0 : a = 0
  · left; exact maxD_zero _ (ha.trans ha0)
  have hd : 1 ≤ a ^ b := Nat.pow_pos (by omega)
  have hst : s < t := by
    false_or_by_contra
    have : t * t ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, t = s + j := ⟨t - s, by omega⟩
  have hj : 1 ≤ j := by omega
  have hexp : (s + j) * (s + j) = s * s + j * (2 * s + j) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.two_mul, Nat.mul_comm j s]; omega
  have hdj : a ^ b = j * (2 * s + j) := by omega
  have hq : a ^ b / j = 2 * s + j := by
    rw [hdj]; exact Nat.mul_div_cancel_left _ (by omega)
  obtain ⟨hJ, hg0⟩ := allgood a b (by omega) (by omega)
  have hjJ : j ≤ J a b := by
    false_or_by_contra
    have : (J a b + 1) * (J a b + 1) ≤ j * (2 * s + j) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hg := hg0 j hj hjJ
  have hm : a ^ b % j = 0 := by rw [hdj]; exact Nat.mul_mod_right _ _
  simp only [good, hm, hq] at hg
  have h2 : j ≤ 2 * s + j := by omega
  simp [h2, ha, hb] at hg
  omega

theorem A096913_3844 : 3844 = 62 * 62 ∧ 3844 + maxD 3844 ^ minD 3844 = 66 * 66 ∧
    0 + maxD 0 ^ minD 0 = 1 * 1 := by decide
