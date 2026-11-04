/-
OEIS A083452: a(n) = (n concatenated n times − n^n)/n.  Conjecture: all terms
are positive for n > 1, i.e. n concatenated with itself n times exceeds n^n.
True (trivial).

`cat n d k` is n written k times in a row, where d is the number of decimal
digits of n (only n < 10^d is used below).

Checked here (core Lean, full statement):
* `cat_ge`: cat n d (k+1) ≥ n·10^(d·k).
* `main`: for n ≥ 2 and n < 10^d, n^n < cat n d n, since
  n^n = n·n^(n-1) < n·(10^d)^(n-1).
Not checked here: nothing.
-/

def cat (n d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => cat n d k * 10 ^ d + n

theorem cat_ge (n d k : Nat) : n * 10 ^ (d * k) ≤ cat n d (k + 1) := by
  induction k with
  | zero => simp [cat]
  | succ k ih =>
    have e : 10 ^ (d * (k + 1)) = 10 ^ (d * k) * 10 ^ d := by
      rw [Nat.mul_succ, Nat.pow_add]
    show n * 10 ^ (d * (k + 1)) ≤ cat n d (k + 1) * 10 ^ d + n
    rw [e, ← Nat.mul_assoc]
    exact Nat.le_add_right_of_le (Nat.mul_le_mul_right _ ih)

theorem main (n d : Nat) (hn : 2 ≤ n) (hd : n < 10 ^ d) : n ^ n < cat n d n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : (m + 1) ^ m < (10 ^ d) ^ m := Nat.pow_lt_pow_left hd (by omega)
  have h2 : (m + 1) ^ (m + 1) = (m + 1) * (m + 1) ^ m := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have h3 : (m + 1) * (m + 1) ^ m < (m + 1) * (10 ^ d) ^ m :=
    Nat.mul_lt_mul_of_pos_left h1 (by omega)
  have h4 := cat_ge (m + 1) d m
  rw [← Nat.pow_mul] at h3
  omega
