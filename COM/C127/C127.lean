/-
COM-C127 (Coman 2013, conjecture 127): every Poulet number P with 5 ∣ P and 3 ∤ P has
some m >= 1 with (P + 5^m)/30 prime. False, non-constructively.

Checked here (core Lean, no Mathlib), for every P = a (mod M) with
a = 19664845, M = 30 * 7 * 13 * 31 * 601 = 50862630:
* `even_not_int`: for even m, 30 does not divide P + 5^m, so (P + 5^m)/30 is not an integer.
* `cover_divides`: for odd m, some q in {7, 13, 31, 601} divides (P + 5^m)/30 = (P + 5^m) / 30
  and 1 < q < (P + 5^m)/30, so the quotient is composite.
* `class_facts`: 5 ∣ a, 3 ∤ a, a odd, gcd(a, M) = 5 (data for Carmichael compatibility).
Not checked here: that the class contains Poulet numbers. It is Carmichael compatible in the
sense of D. Larsen, arXiv:2504.09056 (2025 preprint, unrefereed), Theorem 1, which then gives
infinitely many Carmichael numbers in it; they are Poulet numbers with 5 ∣ P, 3 ∤ P.
No explicit P is known (none below 10^13). Primality of 7, 13, 31, 601 is not used.
-/

def a : Nat := 19664845
def M : Nat := 50862630

/-- (q, o, r): 5^o ≡ 1 (mod q), and q ∣ a + 5^m whenever m ≡ r (mod o). -/
def cover : List (Nat × Nat × Nat) :=
  [(31, 3, 1), (13, 4, 3), (7, 6, 5), (601, 12, 9)]

theorem M_eq : M = 30 * 7 * 13 * 31 * 601 := by decide
theorem class_facts : a % 5 = 0 ∧ a % 3 = 1 ∧ a % 2 = 1 ∧ Nat.gcd a M = 5 := by decide
theorem cover_orders : cover.all (fun t => 5 ^ t.2.1 % t.1 == 1) = true := by decide
theorem cover_classes : cover.all (fun t => (a + 5 ^ t.2.2) % t.1 == 0) = true := by decide
theorem cover_periods :
    cover.all (fun t => 12 % t.2.1 == 0 && M % t.1 == 0 && Nat.gcd 30 t.1 == 1) = true := by
  decide
theorem cover_small : cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ 601)) = true := by decide
theorem cover_odd :
    (List.range 12).all (fun r => r % 2 == 0 || cover.any (fun t => r % t.2.1 == t.2.2)) = true := by
  decide

/-- b^n mod q depends only on n mod o when b^o ≡ 1 (mod q). -/
theorem pow_period (b q o n : Nat) (ho : b ^ o % q = 1) : b ^ n % q = b ^ (n % o) % q := by
  have h := Nat.div_add_mod n o
  conv => lhs; rw [← h, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, ho, Nat.one_pow]
  have hq : q ≠ 1 := by
    intro h1; rw [h1, Nat.mod_one] at ho; exact absurd ho (by decide)
  cases q with
  | zero => simp
  | succ q' =>
    have : 1 % (q' + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.one_mul, Nat.mod_mod]

theorem P_mod (P d : Nat) (hP : P % M = a) (hd : M % d = 0) : P % d = a % d := by
  rw [← Nat.mod_mod_of_dvd P (Nat.dvd_of_mod_eq_zero hd), hP]

theorem pow5_mod3 (m : Nat) : 5 ^ m % 3 = 5 ^ (m % 2) % 3 := pow_period 5 3 2 m (by decide)

theorem even_not_int (P m : Nat) (hP : P % M = a) (hm : m % 2 = 0) : ¬ 30 ∣ P + 5 ^ m := by
  intro h
  have h3 : P % 3 = 1 := by rw [P_mod P 3 hP (by decide)]; decide
  have h5 : 5 ^ m % 3 = 1 := by rw [pow5_mod3, hm]
  have := Nat.mod_eq_zero_of_dvd h
  omega

theorem cover_divides (P m : Nat) (hP : P % M = a) (hm : m % 2 = 1) :
    ∃ t ∈ cover, t.1 ∣ (P + 5 ^ m) / 30 ∧ 1 < t.1 ∧ t.1 < (P + 5 ^ m) / 30 := by
  have hr : m % 12 ∈ List.range 12 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have h1 := List.all_eq_true.mp cover_odd _ hr
  have hm12 : m % 12 % 2 = 1 := by omega
  simp only [hm12, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by decide)
  obtain ⟨t, ht, hcls⟩ := List.any_eq_true.mp h1
  have ho : 5 ^ t.2.1 % t.1 = 1 := by simpa using List.all_eq_true.mp cover_orders t ht
  have hc : (a + 5 ^ t.2.2) % t.1 = 0 := by simpa using List.all_eq_true.mp cover_classes t ht
  have hper := List.all_eq_true.mp cover_periods t ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hper
  obtain ⟨⟨hd12, hdM⟩, hg⟩ := hper
  have hs := List.all_eq_true.mp cover_small t ht
  simp only [decide_eq_true_eq] at hs
  have hcl : m % 12 % t.2.1 = t.2.2 := by simpa using hcls
  have hn : m % t.2.1 = t.2.2 := by
    rw [← Nat.mod_mod_of_dvd m (Nat.dvd_of_mod_eq_zero hd12)]; exact hcl
  have hq : t.1 ∣ P + 5 ^ m := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, P_mod P t.1 hP hdM, pow_period 5 t.1 t.2.1 m ho, hn, ← Nat.add_mod, hc]
  have hP2 : P % 2 = 1 := by rw [P_mod P 2 hP (by decide)]; decide
  have hP3 : P % 3 = 1 := by rw [P_mod P 3 hP (by decide)]; decide
  have hP5 : P % 5 = 0 := by rw [P_mod P 5 hP (by decide)]; decide
  have h52 : 5 ^ m % 2 = 1 := by rw [Nat.pow_mod]; simp
  have h53 : 5 ^ m % 3 = 2 := by rw [pow5_mod3, hm]
  have h55 : 5 ^ m % 5 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.pow_succ]; simp
  have h30 : 30 ∣ P + 5 ^ m := Nat.dvd_of_mod_eq_zero (by omega)
  have hmul : 30 * t.1 ∣ P + 5 ^ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hg h30 hq
  refine ⟨t, ht, Nat.dvd_div_of_mul_dvd hmul, by omega, ?_⟩
  have hPa : a ≤ P := by rw [← hP]; exact Nat.mod_le P M
  have : 602 * 30 ≤ a := by decide
  have hle : 602 * 30 ≤ P + 5 ^ m := Nat.le_trans (by omega) (Nat.le_add_right P (5 ^ m))
  have : 602 ≤ (P + 5 ^ m) / 30 := (Nat.le_div_iff_mul_le (by decide)).mpr hle
  omega
