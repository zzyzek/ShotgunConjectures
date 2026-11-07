import Mathlib
import OpenProblemsLib.Pratt

/-!
# OEIS A114782: the conjecture "a(n) = 0 iff prime(n) + 1 == 0 (mod 3)" is false

A114782(n) = smallest prime of the form 10^k + prime(n) with k >= d, d the number of decimal digits
of prime(n); 0 if there is no such prime. `A114782` below is that definition (n >= 1, prime(1) = 2).

Checked here: p = 48247 = prime(4966) is prime (Pratt certificate, `decide +kernel`), p == 1 (mod 3), and
for every k >= 0 the number 10^k + p has a proper divisor in {7, 11, 13, 37} (covering by the classes
k == 4 (6), 1 (2), 2 (6), 0 (3)). Hence A114782(n) = 0 for the index n with
prime(n) = p, although prime(n) + 1 is not divisible by 3.
Not checked: nothing beyond reading the OEIS definition as `A114782`.
-/

def F (n : Nat) : Nat := 1 * 10 ^ n + 48247

def cover : List (Nat × Nat × Nat) :=
  [(37, 3, 0),
   (11, 2, 1),
   (13, 6, 2),
   (7, 6, 4)]

theorem cover_orders : cover.all (fun t => 10 ^ t.2.1 % t.1 == 1) = true := by decide +kernel
theorem cover_classes : cover.all (fun t => (1 * 10 ^ t.2.2 + 48247) % t.1 == 0) = true := by decide +kernel
theorem cover_periods : cover.all (fun t => 6 % t.2.1 == 0) = true := by decide +kernel
theorem cover_small : cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ 37 ∧ t.2.2 < t.2.1)) = true := by decide +kernel
theorem cover_all : (List.range 6).all (fun r => cover.any (fun t => r % t.2.1 == t.2.2)) = true := by decide +kernel

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
    have hc  : (1 * 10 ^ t.2.2 + 48247) % t.1 = 0 := by simpa using List.all_eq_true.mp cover_classes t ht
    have hd  : t.2.1 ∣ 6 := Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp cover_periods t ht)
    have hcl : n % 6 % t.2.1 = t.2.2 := by simpa using hcls
    have hn : n % t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd n hd]; exact hcl
    apply Nat.dvd_of_mod_eq_zero
    unfold F
    rw [Nat.add_mod, Nat.mul_mod, pow_period t.1 t.2.1 n ho, hn, ← Nat.mul_mod, ← Nat.add_mod, hc]
  · have : 37 < 48247 := by decide +kernel
    unfold F
    have := Nat.le_add_left 48247 (1 * 10 ^ n)
    omega

/-- d(p) = number of decimal digits; A114782(n) per the OEIS name (offset 1). -/
noncomputable def A114782 (n : ℕ) : ℕ := by
  classical
  exact
    let p := Nat.nth Nat.Prime (n - 1)
    if h : ∃ k, (Nat.digits 10 p).length ≤ k ∧ (10 ^ k + p).Prime then 10 ^ (Nat.find h) + p else 0

theorem p_prime : (48247 : ℕ).Prime := by
  apply OpenProblemsLib.prime_of_prattCertifies (cert := [⟨2, 1, []⟩,
  ⟨3, 2, [(2, 1)]⟩,
  ⟨5, 2, [(2, 2)]⟩,
  ⟨11, 2, [(2, 1), (5, 1)]⟩,
  ⟨17, 3, [(2, 4)]⟩,
  ⟨7, 3, [(2, 1), (3, 1)]⟩,
  ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩,
  ⟨48247, 3, [(2, 1), (3, 1), (11, 1), (17, 1), (43, 1)]⟩])
  decide +kernel

theorem never_prime (k : ℕ) : ¬ (10 ^ k + 48247).Prime := by
  obtain ⟨t, -, hd, h1, h2⟩ := cover_divides k
  intro hp
  have := (Nat.prime_def.mp hp).2 t.1 (by simpa [F] using hd)
  unfold F at h2
  omega

theorem A114782_eq_zero_of (n : ℕ) (h : ∀ k, ¬ (10 ^ k + Nat.nth Nat.Prime (n - 1)).Prime) :
    A114782 n = 0 := by
  classical
  unfold A114782
  rw [dite_eq_right_iff]
  rintro ⟨k, -, hk⟩
  exact absurd hk (h k)

/-- Main theorem: an index n with A114782(n) = 0 and prime(n) + 1 not divisible by 3. -/
theorem A114782_conjecture_false :
    ∃ n, A114782 n = 0 ∧ (Nat.nth Nat.Prime (n - 1) + 1) % 3 ≠ 0 := by
  have hn : Nat.nth Nat.Prime (Nat.count Nat.Prime 48247 + 1 - 1) = 48247 := by
    rw [Nat.add_sub_cancel]
    exact Nat.nth_count p_prime
  refine ⟨Nat.count Nat.Prime 48247 + 1, ?_, ?_⟩
  · apply A114782_eq_zero_of
    rw [hn]
    exact never_prime
  · rw [hn]
    norm_num
