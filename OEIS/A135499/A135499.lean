/-
OEIS A135499: numbers whose digit sums at odd and at even positions are equal.
Conjecture (Mathar 2008): every term is a multiple of 11. True.

`f n` = (digits at even positions from the right, counting from 0) minus
(digits at odd positions), as an integer. Equal sums means f n = 0 (counting
positions from the left instead only swaps the two sums).

Checked here (core Lean): `mod11`, n ≡ f n (mod 11) for every n, and
`subsequence`, f n = 0 → 11 ∣ n.
Not checked here: nothing.
-/

/-- digit alternating sum with fuel k (enough when n ≤ k) -/
def g : Nat → Nat → Int
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else ((n % 10 : Nat) : Int) - g k (n / 10)

def f (n : Nat) : Int := g n n

theorem g_mod11 (k : Nat) : ∀ n, n ≤ k → (11 : Int) ∣ (n : Int) - g k n := by
  induction k with
  | zero => intro n hn; have : n = 0 := by omega
            subst this; simp [g]
  | succ k ih =>
    intro n hn
    simp only [g]
    split
    · rename_i h0; subst h0; simp
    · rename_i h0
      have h := ih (n / 10) (by omega)
      have e : (n : Int) = 10 * ((n / 10 : Nat) : Int) + ((n % 10 : Nat) : Int) := by omega
      rw [e]
      omega

theorem mod11 (n : Nat) : (11 : Int) ∣ (n : Int) - f n := g_mod11 n n (Nat.le_refl n)

theorem subsequence (n : Nat) (h : f n = 0) : 11 ∣ n := by
  have := mod11 n
  rw [h, Int.sub_zero] at this
  exact Int.natCast_dvd_natCast.mp this

theorem examples : f 121 = 0 ∧ f 220 = 0 ∧ f 11 = 0 ∧ f 12 ≠ 0 := by decide
