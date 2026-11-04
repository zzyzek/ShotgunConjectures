/-
OEIS A101462 (smallest k with 2^k - prime(n) prime).  Conjecture: the
sequence is defined for all n.  False: for prime(42228) = 509203 (Riesel's
number) 2^k - 509203 is never prime.

Checked here (core Lean):
* `cover_divides`: for every k ≥ 19 some q ∈ {3, 5, 7, 13, 17, 241} divides
  2^k - 509203 and 1 < q < 2^k - 509203 (orders of 2: 2, 4, 3, 12, 8, 24;
  the classes cover Z/24).  For k ≤ 18, 2^k < 509203.
* `p_prime_trial`: 509203 has no divisor in [2, 730] ⊇ [2, 714], and
  714^2 > 509203, so it is prime.
Not checked here: 509203 = prime(42228), i.e. pi(509203) = 42228 (PARI primepi,
certificate/check.py).
-/

def P : Nat := 509203

/-- (q, o, a): o = ord_q(2), and q ∣ 2^k - P whenever k ≡ a (mod o). -/
def cover : List (Nat × Nat × Nat) :=
  [(3, 2, 0), (5, 4, 3), (7, 3, 1), (13, 12, 5), (17, 8, 1), (241, 24, 21)]

theorem cover_orders : cover.all (fun t => 2 ^ t.2.1 % t.1 == 1) = true := by decide
theorem cover_classes : cover.all (fun t => 2 ^ t.2.2 % t.1 == P % t.1) = true := by decide
theorem cover_periods : cover.all (fun t => 24 % t.2.1 == 0) = true := by decide
theorem cover_small : cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ 241 ∧ t.2.2 < t.2.1)) = true := by decide
theorem cover_all : (List.range 24).all (fun r => cover.any (fun t => r % t.2.1 == t.2.2)) = true := by decide

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

theorem cover_divides (k : Nat) (hk : 19 ≤ k) :
    ∃ t ∈ cover, t.1 ∣ 2 ^ k - P ∧ 1 < t.1 ∧ t.1 < 2 ^ k - P := by
  have hr : k % 24 ∈ List.range 24 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have h1 := List.all_eq_true.mp cover_all _ hr
  obtain ⟨t, ht, hcls⟩ := List.any_eq_true.mp h1
  have hs := List.all_eq_true.mp cover_small t ht
  simp only [decide_eq_true_eq] at hs
  have hbig : 2 ^ 19 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h19 : 2 ^ 19 = 524288 := by decide
  have hP : P = 509203 := rfl
  refine ⟨t, ht, ?_, by omega, by omega⟩
  have ho : 2 ^ t.2.1 % t.1 = 1 := by simpa using List.all_eq_true.mp cover_orders t ht
  have hc : 2 ^ t.2.2 % t.1 = P % t.1 := by simpa using List.all_eq_true.mp cover_classes t ht
  have hd : t.2.1 ∣ 24 := Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp cover_periods t ht)
  have hcl : k % 24 % t.2.1 = t.2.2 := by simpa using hcls
  have hn : k % t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd k hd]; exact hcl
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [pow_period t.1 t.2.1 k ho, hn, hc]

theorem p_prime_trial : (∀ i, i < 27 → ∀ j, j < 27 → P % (27 * i + j + 2) ≠ 0) ∧
    27 * 26 + 26 + 2 ≥ 714 ∧ 714 * 714 > P := by decide
