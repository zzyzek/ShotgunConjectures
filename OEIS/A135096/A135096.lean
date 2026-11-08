/-
OEIS A135096, comment (Werner D. Sand): "With any real number c in the interval [L,U] there
exists for each natural number n>2 a natural number m and a prime number p so that
n=floor(m^c)+p.  L = 0.5781296526..., U = 1.3652123889685... (A135097)."

Counterexample: c = 131/100 = 1.31 lies in [L, U] and n = 16 is not floor(m^c) + p for any
m >= 0 and prime p.  For c = 131/100, v = floor(m^c) is the unique v with
v^100 <= m^131 < (v+1)^100.

Checked here:
  * `A135096_c131_n16`: for all m, v, p with v^100 <= m^131 < (v+1)^100 and p prime
    (trial division), v + p <> 16.  Cases m <= 8 by kernel evaluation; for m >= 9,
    m^131 >= 9^131 > 15^100 forces v >= 15, so v + p >= 17.
Not checked here: nothing beyond reading the definition (m = 0 is allowed, which only
weakens the counterexample's hypothesis; floor(m^(a/b)) is encoded by the integer
inequalities above).
-/

def isPrimeB (n : Nat) : Bool :=
  2 ≤ n && (List.range n).all (fun d => d < 2 || n % d != 0)

theorem small_cases : ∀ m, m < 9 → ∀ v, v < 17 → ∀ p, p < 17 →
    (v ^ 100 ≤ m ^ 131 ∧ m ^ 131 < (v + 1) ^ 100 ∧ isPrimeB p = true) → v + p ≠ 16 := by
  decide +kernel

theorem small_p : ∀ p, p < 2 → isPrimeB p = false := by decide

theorem big_gap : 15 ^ 100 < 9 ^ 131 := by decide +kernel

theorem A135096_c131_n16 (m v p : Nat) (h1 : v ^ 100 ≤ m ^ 131) (h2 : m ^ 131 < (v + 1) ^ 100)
    (hp : isPrimeB p = true) : v + p ≠ 16 := by
  intro h
  by_cases hm : m < 9
  · exact small_cases m hm v (by omega) p (by omega) ⟨h1, h2, hp⟩ h
  · have hp2 : 2 ≤ p := by
      false_or_by_contra
      have := small_p p (by omega)
      simp_all
    have a : 9 ^ 131 ≤ m ^ 131 := Nat.pow_le_pow_left (by omega) 131
    have b : (v + 1) ^ 100 ≤ 15 ^ 100 := Nat.pow_le_pow_left (by omega) 100
    have := big_gap
    omega
