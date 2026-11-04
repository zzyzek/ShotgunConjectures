/-
OEIS A088276 (smallest k with 10^k + r a prime ending in r, r the n-th odd
number not divisible by 5, offset 0; 0 if none).  Conjectures: (1) the only
zero entries have r == 2 (mod 3); (2) for r not == 2 (mod 3) there are
infinitely many k with 10^k + r prime.  Both false at r = 9351 (n = 3740),
r == 0 (mod 3).

Checked here (core Lean, full statement for r = 9351): `cover_divides`: for
every k one of 7, 11, 13, 37 divides 10^k + 9351 and is smaller than it, so
10^k + 9351 is never prime (orders of 10: 6, 2, 6, 3; classes cover Z/6).
Not checked here: that 9351 is the entry with index 3740 (count of odd numbers
not divisible by 5 below 9351; certificate/check.py).
-/

def F (n : Nat) : Nat := 1 * 10 ^ n + 9351

def cover : List (Nat × Nat × Nat) :=
  [(7, 6, 0),
   (11, 2, 1),
   (13, 6, 2),
   (37, 3, 1)]

theorem cover_orders : cover.all (fun t => 10 ^ t.2.1 % t.1 == 1) = true := by decide
theorem cover_classes : cover.all (fun t => (1 * 10 ^ t.2.2 + 9351) % t.1 == 0) = true := by decide
theorem cover_periods : cover.all (fun t => 6 % t.2.1 == 0) = true := by decide
theorem cover_small : cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ 37 ∧ t.2.2 < t.2.1)) = true := by decide
theorem cover_all : (List.range 6).all (fun r => cover.any (fun t => r % t.2.1 == t.2.2)) = true := by decide

theorem pow_period (q o n : Nat) (ho : 10 ^ o % q = 1) : 10 ^ n % q = 10 ^ (n % o) % q := by
  have h := Nat.div_add_mod n o
  conv => lhs; rw [← h, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, ho, Nat.one_pow]
  have hq : q ≠ 1 := by
    intro h1; rw [h1, Nat.mod_one] at ho; exact absurd ho (by decide)
  cases q with
  | zero => simp
  | succ q' =>
    have : 1 % (q' + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.one_mul, Nat.mod_mod]

theorem cover_divides (n : Nat) :
    ∃ t ∈ cover, t.1 ∣ F n ∧ 1 < t.1 ∧ t.1 < F n := by
  have hr : n % 6 ∈ List.range 6 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have h1 := List.all_eq_true.mp cover_all _ hr
  obtain ⟨t, ht, hcls⟩ := List.any_eq_true.mp h1
  have hs := List.all_eq_true.mp cover_small t ht
  simp only [decide_eq_true_eq] at hs
  refine ⟨t, ht, ?_, by omega, ?_⟩
  · have ho  : 10 ^ t.2.1 % t.1 = 1 := by simpa using List.all_eq_true.mp cover_orders t ht
    have hc  : (1 * 10 ^ t.2.2 + 9351) % t.1 = 0 := by simpa using List.all_eq_true.mp cover_classes t ht
    have hd  : t.2.1 ∣ 6 := Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp cover_periods t ht)
    have hcl : n % 6 % t.2.1 = t.2.2 := by simpa using hcls
    have hn : n % t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd n hd]; exact hcl
    apply Nat.dvd_of_mod_eq_zero
    unfold F
    rw [Nat.add_mod, Nat.mul_mod, pow_period t.1 t.2.1 n ho, hn, ← Nat.mul_mod, ← Nat.add_mod, hc]
  · have : 37 < 9351 := by decide
    unfold F
    have := Nat.le_add_left 9351 (1 * 10 ^ n)
    omega
