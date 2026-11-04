/-
COM-C125 (Coman 2013, conjecture 125): "for every odd prime p ≠ 5 there are
infinitely many n with 5p + 2^n prime". False for p = 76739471787787.

Checked here (core Lean, no Mathlib):
* `cover_divides`: for every n, some prime q of the covering set divides
  5p + 2^n, and q < 5p + 2^n, so 5p + 2^n is composite for every n.
Not checked here: that p is prime (PARI `isprime`, a proof by APR-CL;
see COM/C125/README.md) and that the q's are prime (they are
3, 7, 13, 17, 19, 37, 73, 109, 241; only divisibility is used below).

Pattern (reusable for any covering argument): finitely many `decide` facts
(orders, classes, the cover of Z/72) plus one periodicity lemma for b^n mod q.
-/

def p : Nat := 76739471787787

/-- (q, o, a): o = ord_q(2), and q ∣ 5p + 2^n whenever n ≡ a (mod o). -/
def cover : List (Nat × Nat × Nat) :=
  [(3, 2, 0), (17, 8, 1), (7, 3, 0), (19, 18, 5), (13, 12, 7), (73, 9, 2),
   (241, 24, 13), (37, 36, 35), (109, 36, 17)]

theorem cover_orders : cover.all (fun t => 2 ^ t.2.1 % t.1 == 1) = true := by decide
theorem cover_classes : cover.all (fun t => (5 * p + 2 ^ t.2.2) % t.1 == 0) = true := by decide
theorem cover_periods : cover.all (fun t => 72 % t.2.1 == 0) = true := by decide
theorem cover_small : cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ 241 ∧ t.2.2 < t.2.1)) = true := by decide
theorem cover_all : (List.range 72).all (fun r => cover.any (fun t => r % t.2.1 == t.2.2)) = true := by decide

/-- 2^n mod q depends only on n mod o when 2^o ≡ 1 (mod q). -/
theorem pow_period (q o n : Nat) (ho : 2 ^ o % q = 1) : 2 ^ n % q = 2 ^ (n % o) % q := by
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
    ∃ t ∈ cover, t.1 ∣ 5 * p + 2 ^ n ∧ 1 < t.1 ∧ t.1 < 5 * p + 2 ^ n := by
  have hr : n % 72 ∈ List.range 72 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have h1 := List.all_eq_true.mp cover_all _ hr
  obtain ⟨t, ht, hcls⟩ := List.any_eq_true.mp h1
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · have ho  : 2 ^ t.2.1 % t.1 = 1 := by simpa using List.all_eq_true.mp cover_orders t ht
    have hc  : (5 * p + 2 ^ t.2.2) % t.1 = 0 := by simpa using List.all_eq_true.mp cover_classes t ht
    have hd  : t.2.1 ∣ 72 := Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp cover_periods t ht)
    have hcl : n % 72 % t.2.1 = t.2.2 := by simpa using hcls
    have hs  := List.all_eq_true.mp cover_small t ht
    simp only [decide_eq_true_eq] at hs
    have hn : n % t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd n hd]; exact hcl
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, pow_period t.1 t.2.1 n ho, hn, ← Nat.add_mod, hc]
  · have hs := List.all_eq_true.mp cover_small t ht
    simp only [decide_eq_true_eq] at hs
    omega
  · have hs := List.all_eq_true.mp cover_small t ht
    simp only [decide_eq_true_eq] at hs
    have : 241 < 5 * p := by decide
    have := Nat.le_add_right (5 * p) (2 ^ n)
    omega
