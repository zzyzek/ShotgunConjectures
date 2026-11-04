/-
OEIS A112992 (k with ceiling(2^(2^k mod k)/3) odd).  Conjecture: the odd values
of ceiling(2^(2^k mod k)/3) are Jacobsthal numbers and the even values are
1 plus a Jacobsthal number.  True for every exponent r, not just r = 2^k mod k.

J = Jacobsthal numbers (A001045): J(0) = 0, J(1) = 1, J(n+2) = J(n+1) + 2 J(n).
ceiling(2^r/3) = (2^r + 2)/3 (natural-number division).

Checked here (core Lean, full statement):
* `J_closed`: 3 J(2k) + 1 = 4^k and 3 J(2k+1) = 2·4^k + 1.
* `J_odd`: J(n) is odd for n ≥ 1.
* `main`: for every r, if ceiling(2^r/3) is odd it equals some J(i), and if it
  is even it equals J(i) + 1 for some i (r odd: J(r); r even ≥ 2: J(r) + 1;
  r = 0: 1 = J(1)).
Not checked here: nothing.
-/

def J : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => J (n + 1) + 2 * J n

theorem J_rec (n : Nat) : J (n + 2) = J (n + 1) + 2 * J n := by simp only [J]

theorem J_closed (k : Nat) : 3 * J (2 * k) + 1 = 4 ^ k ∧ 3 * J (2 * k + 1) = 2 * 4 ^ k + 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have e1 : J (2 * (k + 1)) = J (2 * k + 1) + 2 * J (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]; exact J_rec (2 * k)
    have e2 : J (2 * (k + 1) + 1) = J (2 * (k + 1)) + 2 * J (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
          show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      exact J_rec (2 * k + 1)
    have hp : 4 ^ (k + 1) = 4 ^ k * 4 := by rw [Nat.pow_succ]
    omega

theorem J_odd : ∀ n, J (n + 1) % 2 = 1
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have h : J (n + 2) % 2 = 1 := J_odd (n + 1)
    have e : J (n + 2 + 1) = J (n + 2) + 2 * J (n + 1) := J_rec (n + 1)
    omega

theorem pow2_even (k : Nat) : 2 ^ (2 * k) = 4 ^ k := by rw [Nat.pow_mul]
theorem pow2_odd (k : Nat) : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [Nat.pow_succ, Nat.pow_mul, Nat.mul_comm]

theorem main (r : Nat) :
    ((2 ^ r + 2) / 3 % 2 = 1 → ∃ i, (2 ^ r + 2) / 3 = J i) ∧
    ((2 ^ r + 2) / 3 % 2 = 0 → ∃ i, (2 ^ r + 2) / 3 = J i + 1) := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, r = 2 * k ∨ r = 2 * k + 1 := ⟨r / 2, by omega⟩
  · have h := (J_closed k).1
    rw [pow2_even]
    have hc : (4 ^ k + 2) / 3 = J (2 * k) + 1 := by omega
    rw [hc]
    cases k with
    | zero => exact ⟨fun _ => ⟨1, by decide⟩, fun h0 => absurd h0 (by decide)⟩
    | succ k =>
      have ho := J_odd (2 * k + 1)
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at ho
      exact ⟨fun h1 => absurd h1 (by omega), fun _ => ⟨2 * (k + 1), rfl⟩⟩
  · have h := (J_closed k).2
    rw [pow2_odd]
    have hc : (2 * 4 ^ k + 2) / 3 = J (2 * k + 1) := by omega
    rw [hc]
    have ho := J_odd (2 * k)
    exact ⟨fun _ => ⟨2 * k + 1, rfl⟩, fun h0 => absurd h0 (by omega)⟩
