/-
OEIS A217738: numbers k such that Fibonacci(k) is divisible by k*(k+1).
Conjecture (entry): all terms are divisible by 12 (and the sequence is infinite).

Checked here (core Lean, no imports):
* `fib` is the Fibonacci sequence, fib 0 = 0, fib 1 = 1.
* `fib_mod_two`: 2 ∣ fib n ↔ 3 ∣ n;  `fib_mod_three`: 3 ∣ fib n ↔ 4 ∣ n.
* `A217738_div12`: if k * (k+1) ∣ fib k then 12 ∣ k.
  (2 divides k(k+1), so 2 ∣ fib k and 3 ∣ k; then 3 ∣ k ∣ fib k, so 4 ∣ k.)
Not checked here: the infinitude part of the conjecture, which is open.
-/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib n + fib (n + 1)

theorem fib_add_three (n : Nat) : fib (n + 3) = 2 * fib (n + 1) + fib n := by
  show fib (n + 1) + fib (n + 2) = 2 * fib (n + 1) + fib n
  show fib (n + 1) + (fib n + fib (n + 1)) = 2 * fib (n + 1) + fib n
  omega

theorem fib_add_four (n : Nat) : fib (n + 4) = 3 * fib (n + 1) + 2 * fib n := by
  show fib (n + 2) + fib (n + 3) = 3 * fib (n + 1) + 2 * fib n
  rw [fib_add_three]
  show (fib n + fib (n + 1)) + (2 * fib (n + 1) + fib n) = 3 * fib (n + 1) + 2 * fib n
  omega

theorem fib_mod_two_aux (n : Nat) :
    (fib n % 2 = 0 ↔ n % 3 = 0) ∧ (fib (n + 1) % 2 = 0 ↔ (n + 1) % 3 = 0) ∧
    (fib (n + 2) % 2 = 0 ↔ (n + 2) % 3 = 0) := by
  induction n with
  | zero => decide
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    have e := fib_add_three k
    have : fib (k + 1 + 2) = fib (k + 3) := rfl
    rw [this, e]
    constructor
    · intro h; have := h0.mp (by omega); omega
    · intro h; have := h0.mpr (by omega); omega

theorem fib_mod_two (n : Nat) : 2 ∣ fib n ↔ 3 ∣ n := by
  have := (fib_mod_two_aux n).1
  constructor
  · intro h; exact Nat.dvd_of_mod_eq_zero (this.mp (Nat.mod_eq_zero_of_dvd h))
  · intro h; exact Nat.dvd_of_mod_eq_zero (this.mpr (Nat.mod_eq_zero_of_dvd h))

theorem fib_mod_three_aux (n : Nat) :
    (fib n % 3 = 0 ↔ n % 4 = 0) ∧ (fib (n + 1) % 3 = 0 ↔ (n + 1) % 4 = 0) ∧
    (fib (n + 2) % 3 = 0 ↔ (n + 2) % 4 = 0) ∧
    (fib (n + 3) % 3 = 0 ↔ (n + 3) % 4 = 0) := by
  induction n with
  | zero => decide
  | succ k ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨h1, h2, h3, ?_⟩
    have e := fib_add_four k
    have : fib (k + 1 + 3) = fib (k + 4) := rfl
    rw [this, e]
    constructor
    · intro h; have := h0.mp (by omega); omega
    · intro h; have := h0.mpr (by omega); omega

theorem fib_mod_three (n : Nat) : 3 ∣ fib n ↔ 4 ∣ n := by
  have := (fib_mod_three_aux n).1
  constructor
  · intro h; exact Nat.dvd_of_mod_eq_zero (this.mp (Nat.mod_eq_zero_of_dvd h))
  · intro h; exact Nat.dvd_of_mod_eq_zero (this.mpr (Nat.mod_eq_zero_of_dvd h))

theorem A217738_div12 (k : Nat) (h : k * (k + 1) ∣ fib k) : 12 ∣ k := by
  have h2 : 2 ∣ k * (k + 1) := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.mul_mod, Nat.add_mod]
    have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h0 | h0 <;> rw [h0]
  have h3k : 3 ∣ k := (fib_mod_two k).mp (Nat.dvd_trans h2 h)
  have hk : k ∣ fib k := Nat.dvd_trans (Nat.dvd_mul_right k (k + 1)) h
  have h4k : 4 ∣ k := (fib_mod_three k).mp (Nat.dvd_trans h3k hk)
  omega

/-- The first listed term. -/
theorem A217738_60 : 60 * 61 ∣ fib 60 := by decide
