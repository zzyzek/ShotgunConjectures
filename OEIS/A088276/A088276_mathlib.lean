import Mathlib

/-
OEIS A088276 (Mathlib): a(n) = smallest k with 10^k + r a prime ending in r, where r is the
n-th odd number not divisible by 5 (offset 0), and a(n) = 0 if there is none. Conjectures:
(1) the only zero entries have r ≡ 2 (mod 3); (2) for r ≢ 2 (mod 3) there are infinitely
many k with 10^k + r prime. README result: both false at r = 9351, index n = 3740.

Main theorem `A088276_main`: with r = `Nat.nth (fun k => k % 2 = 1 ∧ k % 5 ≠ 0)` (0-indexed,
matching the entry's offset 0), r 3740 = 9351, 9351 % 3 = 0, and 10^k + r 3740 is prime for no
k. So a(3740) = 0 with r ≡ 0 (mod 3), refuting (1) (`A088276_conj1_false`), and the set of k
with 10^k + r 3740 prime is empty, refuting (2) (`A088276_conj2_false`).

Proof. Covering congruence restated from the core file A088276.lean: for every k one of
7, 11, 13, 37 divides 10^k + 9351 and is smaller. The index: `Nat.count` of the predicate
below 9351 is 3740 (kernel evaluation in 9 blocks of 1039), and `Nat.nth_count`.

Outside Lean: nothing.
-/

/-! ### The covering congruence (from A088276.lean) -/

def A088276_F (n : Nat) : Nat := 1 * 10 ^ n + 9351

def A088276_cover : List (Nat × Nat × Nat) :=
  [(7, 6, 0),
   (11, 2, 1),
   (13, 6, 2),
   (37, 3, 1)]

theorem A088276_cover_orders : A088276_cover.all (fun t => 10 ^ t.2.1 % t.1 == 1) = true := by
  decide
theorem A088276_cover_classes :
    A088276_cover.all (fun t => (1 * 10 ^ t.2.2 + 9351) % t.1 == 0) = true := by decide
theorem A088276_cover_periods : A088276_cover.all (fun t => 6 % t.2.1 == 0) = true := by decide
theorem A088276_cover_small :
    A088276_cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ 37 ∧ t.2.2 < t.2.1)) = true := by decide
theorem A088276_cover_all :
    (List.range 6).all (fun r => A088276_cover.any (fun t => r % t.2.1 == t.2.2)) = true := by
  decide

theorem A088276_pow_period (q o n : Nat) (ho : 10 ^ o % q = 1) :
    10 ^ n % q = 10 ^ (n % o) % q := by
  have h := Nat.div_add_mod n o
  conv => lhs; rw [← h, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, ho, Nat.one_pow]
  have hq : q ≠ 1 := by
    intro h1; rw [h1, Nat.mod_one] at ho; exact absurd ho (by decide)
  cases q with
  | zero => simp
  | succ q' =>
    have : 1 % (q' + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.one_mul, Nat.mod_mod]

theorem A088276_cover_divides (n : Nat) :
    ∃ t ∈ A088276_cover, t.1 ∣ A088276_F n ∧ 1 < t.1 ∧ t.1 < A088276_F n := by
  have hr : n % 6 ∈ List.range 6 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have h1 := List.all_eq_true.mp A088276_cover_all _ hr
  obtain ⟨t, ht, hcls⟩ := List.any_eq_true.mp h1
  have hs := List.all_eq_true.mp A088276_cover_small t ht
  simp only [decide_eq_true_eq] at hs
  refine ⟨t, ht, ?_, by omega, ?_⟩
  · have ho  : 10 ^ t.2.1 % t.1 = 1 := by
      simpa using List.all_eq_true.mp A088276_cover_orders t ht
    have hc  : (1 * 10 ^ t.2.2 + 9351) % t.1 = 0 := by
      simpa using List.all_eq_true.mp A088276_cover_classes t ht
    have hd  : t.2.1 ∣ 6 :=
      Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp A088276_cover_periods t ht)
    have hcl : n % 6 % t.2.1 = t.2.2 := by simpa using hcls
    have hn : n % t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd n hd]; exact hcl
    apply Nat.dvd_of_mod_eq_zero
    unfold A088276_F
    rw [Nat.add_mod, Nat.mul_mod, A088276_pow_period t.1 t.2.1 n ho, hn, ← Nat.mul_mod,
      ← Nat.add_mod, hc]
  · unfold A088276_F
    have := Nat.le_add_left 9351 (1 * 10 ^ n)
    omega

theorem A088276_never_prime (k : ℕ) : ¬ (10 ^ k + 9351).Prime := by
  obtain ⟨t, _, hd, h1, h2⟩ := A088276_cover_divides k
  have e : A088276_F k = 10 ^ k + 9351 := by simp [A088276_F]
  rw [e] at hd h2
  intro hp
  rcases hp.eq_one_or_self_of_dvd _ hd with h | h <;> omega

/-! ### The index 3740 -/

def A088276_cnt (f : ℕ → Bool) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => A088276_cnt f a i + (if f (a + i) then 1 else 0)

def A088276_blk (f : ℕ → Bool) (a B : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => A088276_blk f a B j + A088276_cnt f (a + B * j) B

theorem A088276_count_cnt (f : ℕ → Bool) (a : ℕ) :
    ∀ n, Nat.count (fun i => f (a + i) = true) n = A088276_cnt f a n
  | 0 => by simp [A088276_cnt]
  | n + 1 => by rw [Nat.count_succ, A088276_count_cnt f a n, A088276_cnt]

theorem A088276_count_blk (f : ℕ → Bool) (a B : ℕ) :
    ∀ m, Nat.count (fun i => f (a + i) = true) (B * m) = A088276_blk f a B m
  | 0 => by simp [A088276_blk]
  | m + 1 => by
    rw [Nat.mul_succ, Nat.count_add, A088276_count_blk f a B m, A088276_blk]
    congr 1
    rw [← A088276_count_cnt]
    simp only [Nat.add_assoc]

theorem A088276_count_congr {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] :
    ∀ n, (∀ i < n, (p i ↔ q i)) → Nat.count p n = Nat.count q n
  | 0, _ => by simp
  | n + 1, h => by
    rw [Nat.count_succ, Nat.count_succ, A088276_count_congr n (fun i hi => h i (by omega))]
    by_cases hp : p n
    · simp [hp, (h n (by omega)).mp hp]
    · have : ¬ q n := fun hq => hp ((h n (by omega)).mpr hq)
      simp [hp, this]

/-- The n-th (0-indexed) odd number not divisible by 5. -/
noncomputable def A088276_r (n : ℕ) : ℕ := Nat.nth (fun k => k % 2 = 1 ∧ k % 5 ≠ 0) n

theorem A088276_count : Nat.count (fun k => k % 2 = 1 ∧ k % 5 ≠ 0) (1039 * 9) = 3740 := by
  rw [A088276_count_congr (q := fun i => (fun k => k % 2 == 1 && k % 5 != 0) (0 + i) = true)
    (1039 * 9) (fun i _ => by simp)]
  refine (A088276_count_blk (fun k => k % 2 == 1 && k % 5 != 0) 0 1039 9).trans ?_
  decide +kernel

theorem A088276_index : A088276_r 3740 = 9351 := by
  have h := Nat.nth_count (p := fun k => k % 2 = 1 ∧ k % 5 ≠ 0) (n := 9351) (by decide)
  rw [show (9351 : ℕ) = 1039 * 9 by norm_num, A088276_count] at h
  exact h

theorem A088276_main : A088276_r 3740 = 9351 ∧ 9351 % 3 = 0 ∧
    ∀ k : ℕ, ¬ (10 ^ k + A088276_r 3740).Prime := by
  refine ⟨A088276_index, by norm_num, fun k => ?_⟩
  rw [A088276_index]; exact A088276_never_prime k

theorem A088276_conj1_false :
    ¬ ∀ n : ℕ, (∀ k : ℕ, ¬ (10 ^ k + A088276_r n).Prime) → A088276_r n % 3 = 2 := by
  intro h
  have := h 3740 A088276_main.2.2
  rw [A088276_index] at this
  norm_num at this

theorem A088276_conj2_false :
    ¬ ∀ n : ℕ, A088276_r n % 3 ≠ 2 →
      Set.Infinite {k : ℕ | (10 ^ k + A088276_r n).Prime} := by
  intro h
  have hi := h 3740 (by rw [A088276_index]; norm_num)
  have he : {k : ℕ | (10 ^ k + A088276_r 3740).Prime} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun k hk => A088276_main.2.2 k hk)
  rw [he] at hi
  exact hi Set.finite_empty
