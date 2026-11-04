/-
OEIS A182334: triangular numbers that differ from a square by 1 (offset 1:
0, 1, 3, 10, 15, 120, 325, 528, 4095, 11026, 17955, 139128, ...).
Formula printed without range (Greathouse 2012, conjecture):
a(n) = 35a(n-3) - 35a(n-6) + a(n-9). False as printed: it fails at n = 10
(a(10) = 11026, right side 11025) and n = 11 (17955 versus 17956). It holds
for n ≥ 12 (Pell classes of x^2 - 8s^2 = 9 and -7, x = 2k + 1, unit 3 + √8;
checked numerically to 10^60, see README).

Checked here (core Lean, `decide +kernel`): the triangular numbers T(k),
k < 190, that are s^2 ± 1 are exactly the first 11 terms (so these are
a(1..11), since T(190) > 17955), and the two failures.
Not checked here: the corrected statement for n ≥ 12.
-/

def isSq (n : Nat) : Bool := Nat.sqrt n * Nat.sqrt n == n
def tri (k : Nat) : Nat := k * (k + 1) / 2
def good (t : Nat) : Bool := isSq (t + 1) || (1 ≤ t && isSq (t - 1))

def terms : List Nat := ((List.range 190).map tri).filter good

theorem first_terms : terms = [0, 1, 3, 10, 15, 120, 325, 528, 4095, 11026, 17955] := by decide +kernel
theorem beyond : tri 190 > 17955 := by decide

def a (n : Nat) : Nat := terms.getD (n - 1) 0

theorem fails_10 : a 10 ≠ 35 * a 7 - 35 * a 4 + a 1 := by decide +kernel
theorem fails_11 : a 11 + 35 * a 5 ≠ 35 * a 8 + a 2 := by decide +kernel
theorem values : a 10 = 11026 ∧ 35 * a 7 - 35 * a 4 + a 1 = 11025 ∧ a 11 = 17955 ∧
    35 * a 8 - 35 * a 5 + a 2 = 17956 := by decide +kernel
