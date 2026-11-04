/-
OEIS A176494: least m ≥ 1 with |2^m - prime(n)| prime. Conjecture
(Shevelev 2010): for every odd prime p some |2^m - p|, m ≥ 1, is prime.
False: p = 509203 is prime and |2^m - p| is composite for every m ≥ 1.

Covering congruences: q ∈ {3, 5, 7, 13, 17, 241} has ord_q(2) = o dividing 24,
and q ∣ 2^m - p (as integers) whenever m ≡ c (mod o), because 2^c ≡ p (mod q).
The classes cover Z/24. Since |2^m - p| ≥ 15085 > 241 for every m, the
covering prime is a proper factor.

Checked here (core Lean, axioms propext and Quot.sound at most):
* `p_prime`: no d with 2 ≤ d ≤ 713 divides p, and 714^2 > p (trial division),
  so p is prime;
* `cover_divides`: for every m, some q of the cover divides |2^m - p|
  (written with truncated subtraction, both cases) and 1 < q < |2^m - p|.
Not checked here: nothing.
-/

def p : Nat := 509203

/-- `noDiv n d` is true iff no k with 2 ≤ k ≤ d divides n. -/
def noDiv (n : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | d + 2 => (n % (d + 2) != 0) && noDiv n (d + 1)

theorem noDiv_spec (n d : Nat) (h : noDiv n d = true) : ∀ k, 2 ≤ k → k ≤ d → n % k ≠ 0 := by
  induction d with
  | zero => intro k h1 h2; omega
  | succ d ih =>
    intro k h1 h2
    cases d with
    | zero => omega
    | succ d =>
      simp only [noDiv, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.lt_or_ge k (d + 2) with hk | hk
      · exact ih h.2 k h1 (by omega)
      · have : k = d + 2 := by omega
        subst this; exact h.1

theorem p_trial : noDiv p 713 = true := by decide +kernel
theorem p_sqrt : 714 * 714 > p := by decide

theorem p_prime (k : Nat) (hk : k ∣ p) : k = 1 ∨ k = p := by
  have hp : 0 < p := by decide
  have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hk hp
  obtain ⟨c, hc⟩ := hk
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, Nat.mul_zero] at hc; exact absurd hc (by decide)
    · exact h0
  have nd := noDiv_spec p 713 p_trial
  by_cases h1 : k = 1
  · exact Or.inl h1
  by_cases h2 : c = 1
  · right; rw [hc, h2, Nat.mul_one]
  exfalso
  rcases Nat.lt_or_ge k 714 with hk7 | hk7
  · exact nd k (by omega) (by omega) (by rw [hc]; exact Nat.mul_mod_right k c)
  · rcases Nat.lt_or_ge c 714 with hc7 | hc7
    · exact nd c (by omega) (by omega) (by rw [hc, Nat.mul_comm]; exact Nat.mul_mod_right c k)
    · have : 714 * 714 ≤ k * c := Nat.mul_le_mul (by omega) (by omega)
      have := p_sqrt
      omega

/-- (q, o, c): o = ord_q(2), and 2^c ≡ p (mod q). -/
def cover : List (Nat × Nat × Nat) :=
  [(3, 2, 0), (5, 4, 3), (7, 3, 1), (13, 12, 5), (17, 8, 1), (241, 24, 21)]

theorem cover_orders : cover.all (fun t => 2 ^ t.2.1 % t.1 == 1) = true := by decide
theorem cover_classes : cover.all (fun t => 2 ^ t.2.2 % t.1 == p % t.1) = true := by decide
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

/-- |2^m - p| written with truncated subtraction. -/
def F (m : Nat) : Nat := if p ≤ 2 ^ m then 2 ^ m - p else p - 2 ^ m

theorem F_big (m : Nat) : 241 < F m := by
  unfold F
  rcases Nat.lt_or_ge m 19 with h | h
  · have : 2 ^ m ≤ 2 ^ 18 := Nat.pow_le_pow_right (by decide) (by omega)
    have h18 : 2 ^ 18 + 241 < p := by decide
    simp only [show ¬ (p ≤ 2 ^ m) from by omega, ite_false]; omega
  · have : 2 ^ 19 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) h
    have h19 : p + 241 < 2 ^ 19 := by decide
    simp only [show p ≤ 2 ^ m from by omega, ite_true]; omega

theorem cover_divides (m : Nat) : ∃ t ∈ cover, t.1 ∣ F m ∧ 1 < t.1 ∧ t.1 < F m := by
  have hr : m % 24 ∈ List.range 24 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have h1 := List.all_eq_true.mp cover_all _ hr
  obtain ⟨t, ht, hcls⟩ := List.any_eq_true.mp h1
  have hs := List.all_eq_true.mp cover_small t ht
  simp only [decide_eq_true_eq] at hs
  have hb := F_big m
  refine ⟨t, ht, ?_, by omega, by omega⟩
  have ho  : 2 ^ t.2.1 % t.1 = 1 := by simpa using List.all_eq_true.mp cover_orders t ht
  have hc  : 2 ^ t.2.2 % t.1 = p % t.1 := by simpa using List.all_eq_true.mp cover_classes t ht
  have hd  : t.2.1 ∣ 24 := Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp cover_periods t ht)
  have hcl : m % 24 % t.2.1 = t.2.2 := by simpa using hcls
  have hn : m % t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd m hd]; exact hcl
  have hm : 2 ^ m % t.1 = p % t.1 := by rw [pow_period t.1 t.2.1 m ho, hn, hc]
  apply Nat.dvd_of_mod_eq_zero
  unfold F
  split
  · exact Nat.sub_mod_eq_zero_of_mod_eq hm
  · exact Nat.sub_mod_eq_zero_of_mod_eq hm.symm
