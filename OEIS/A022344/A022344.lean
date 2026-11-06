/-
OEIS A022344 (Wechsler's "J determinant"), conjecture of K. J. Ramsey (2007): every Fibonacci
sequence appears in a row of the Wythoff array, whose characteristic |F(i)^2 - F(i-1)F(i+1)|
is a(row); for Fibonacci sequences F1, F2 and fixed j, F3(i) = F1(i)F2(j+1) - F1(i+1)F2(j)
is a Fibonacci sequence that appears in row p with a(p) = a(n)a(m).

Checked here (core Lean, no imports): the algebra.
* `D_succ`, `char_const`: D(i) = F(i+1)^2 - F(i)F(i+2) changes sign at each step, so the
  characteristic |D| does not depend on i.
* `F3_fib`: F3 satisfies the Fibonacci recurrence.
* `D_F3`: D_{F3}(i) = D_{F1}(i) * D_{F2}(j); `char_F3`: char F3 = char F1 * char F2.
Not checked here: that every eventually positive Fibonacci sequence is a row tail of the
Wythoff array (Morrison 1980), that row n has characteristic a(n), and that F3 is eventually
of constant sign (so |F3|, not F3 itself, is the row of the Wythoff array when F3 < 0).
-/

namespace OEIS_A022344

def IsFib (f : Nat → Int) : Prop := ∀ i, f (i + 2) = f (i + 1) + f i

def D (f : Nat → Int) (i : Nat) : Int := f (i + 1) * f (i + 1) - f i * f (i + 2)

theorem D_succ (f : Nat → Int) (hf : IsFib f) (i : Nat) : D f (i + 1) = - D f i := by
  unfold D
  have h2 := hf i
  have h3 := hf (i + 1)
  rw [show i + 1 + 1 = i + 2 from rfl, show i + 1 + 2 = i + 3 from rfl] at *
  rw [h3, h2]
  grind

theorem char_const (f : Nat → Int) (hf : IsFib f) (i : Nat) : (D f i).natAbs = (D f 0).natAbs := by
  induction i with
  | zero => rfl
  | succ i ih => rw [D_succ f hf i, Int.natAbs_neg, ih]

def F3 (F1 F2 : Nat → Int) (j : Nat) (i : Nat) : Int := F1 i * F2 (j + 1) - F1 (i + 1) * F2 j

theorem F3_fib (F1 F2 : Nat → Int) (j : Nat) (h1 : IsFib F1) : IsFib (F3 F1 F2 j) := by
  intro i
  unfold F3
  have a := h1 i
  have b := h1 (i + 1)
  rw [show i + 2 + 1 = i + 3 from rfl]
  rw [show i + 1 + 2 = i + 3 from rfl] at b
  rw [show i + 1 + 1 = i + 2 from rfl, b, a]
  grind

theorem D_F3 (F1 F2 : Nat → Int) (j : Nat) (h1 : IsFib F1) (h2 : IsFib F2) (i : Nat) :
    D (F3 F1 F2 j) i = D F1 i * D F2 j := by
  unfold D F3
  have a := h1 i
  have b := h1 (i + 1)
  have c := h2 j
  rw [show i + 1 + 2 = i + 3 from rfl] at b
  rw [show i + 1 + 1 = i + 2 from rfl, show i + 2 + 1 = i + 3 from rfl, b, a, c]
  grind

theorem char_F3 (F1 F2 : Nat → Int) (j : Nat) (h1 : IsFib F1) (h2 : IsFib F2) (i : Nat) :
    (D (F3 F1 F2 j) i).natAbs = (D F1 0).natAbs * (D F2 0).natAbs := by
  rw [D_F3 F1 F2 j h1 h2 i, Int.natAbs_mul, char_const F1 h1 i, char_const F2 h2 j]

/-- The sign caveat: F1 = F2 = Fibonacci numbers, j = 1 gives F3(i) = -F(i-1) < 0 for i ≥ 2. -/
def fib : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib n

theorem F3_negative_example : F3 fib fib 1 5 = -3 := by decide

end OEIS_A022344

open OEIS_A022344
