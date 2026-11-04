import OpenProblemsLib

/-
COM-C125 (Mathlib). Coman's conjecture 125: for every odd prime p ≠ 5 there are infinitely many
n with 5p + 2^n prime. README result: false for the prime p = 76739471787787, since
5p + 2^n is composite for every n ≥ 0.

Main theorem `C125_main`: `Nat.Prime 76739471787787`, it is odd and ≠ 5, and for every n,
`5 * 76739471787787 + 2 ^ n` is not prime. `C125_conjecture_false` is the negation of the
conjecture, with "infinitely many" as `Set.Infinite`.

Proof. Primality of p by a Pratt certificate (tools/pratt_cert.py, checked by
`prime_of_prattCertifies` with `decide +kernel`). Compositeness by the covering congruence of
the core file lean, restated here: the nine (q, ord_q 2, class) triples cover Z/72, and
each q (≤ 241) divides 5p + 2^n on its class and is smaller than 5p + 2^n.

Outside Lean: nothing.
-/

open OpenProblemsLib


def p : Nat := 76739471787787

/-- Pratt certificate for p (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨11, 2, [(2, 1), (5, 1)]⟩,
   ⟨23, 5, [(2, 1), (11, 1)]⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨751, 3, [(2, 1), (3, 1), (5, 3)]⟩,
   ⟨47, 5, [(2, 1), (23, 1)]⟩,
   ⟨181, 2, [(2, 2), (3, 2), (5, 1)]⟩,
   ⟨170141, 2, [(2, 2), (5, 1), (47, 1), (181, 1)]⟩,
   ⟨340283, 2, [(2, 1), (170141, 1)]⟩,
   ⟨680567, 5, [(2, 1), (340283, 1)]⟩,
   ⟨556083128897, 3, [(2, 6), (17, 1), (751, 1), (680567, 1)]⟩,
   ⟨76739471787787, 2, [(2, 1), (3, 1), (23, 1), (556083128897, 1)]⟩]

theorem p_prime : p.Prime := prime_of_prattCertifies p cert (by decide +kernel)

/-! ### The covering congruence (from lean) -/

/-- (q, o, a): o = ord_q(2), and q ∣ 5p + 2^n whenever n ≡ a (mod o). -/
def cover : List (Nat × Nat × Nat) :=
  [(3, 2, 0), (17, 8, 1), (7, 3, 0), (19, 18, 5), (13, 12, 7), (73, 9, 2),
   (241, 24, 13), (37, 36, 35), (109, 36, 17)]

theorem cover_orders : cover.all (fun t => 2 ^ t.2.1 % t.1 == 1) = true := by decide +kernel
theorem cover_classes : cover.all (fun t => (5 * p + 2 ^ t.2.2) % t.1 == 0) = true := by
  decide +kernel
theorem cover_periods : cover.all (fun t => 72 % t.2.1 == 0) = true := by decide +kernel
theorem cover_small :
    cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ 241 ∧ t.2.2 < t.2.1)) = true := by decide +kernel
theorem cover_all :
    (List.range 72).all (fun r => cover.any (fun t => r % t.2.1 == t.2.2)) = true := by
  decide +kernel

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
  have hs := List.all_eq_true.mp cover_small t ht
  simp only [decide_eq_true_eq] at hs
  refine ⟨t, ht, ?_, by omega, ?_⟩
  · have ho  : 2 ^ t.2.1 % t.1 = 1 := by simpa using List.all_eq_true.mp cover_orders t ht
    have hc  : (5 * p + 2 ^ t.2.2) % t.1 = 0 := by
      simpa using List.all_eq_true.mp cover_classes t ht
    have hd  : t.2.1 ∣ 72 :=
      Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp cover_periods t ht)
    have hcl : n % 72 % t.2.1 = t.2.2 := by simpa using hcls
    have hn : n % t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd n hd]; exact hcl
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, pow_period t.1 t.2.1 n ho, hn, ← Nat.add_mod, hc]
  · have : 241 < 5 * p := by decide +kernel
    have := Nat.le_add_right (5 * p) (2 ^ n)
    omega

theorem never_prime (n : ℕ) : ¬ (5 * p + 2 ^ n).Prime := by
  obtain ⟨t, _, hd, h1, h2⟩ := cover_divides n
  intro hp
  rcases hp.eq_one_or_self_of_dvd _ hd with h | h <;> omega


theorem C125_main : Nat.Prime 76739471787787 ∧ 76739471787787 ≠ 2 ∧ 76739471787787 ≠ 5 ∧
    ∀ n : ℕ, ¬ (5 * 76739471787787 + 2 ^ n).Prime :=
  ⟨p_prime, by decide, by decide, never_prime⟩

theorem C125_conjecture_false :
    ¬ ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → Set.Infinite {n : ℕ | (5 * p + 2 ^ n).Prime} := by
  intro h
  have hi := h 76739471787787 C125_main.1 C125_main.2.1 C125_main.2.2.1
  have he : {n : ℕ | (5 * 76739471787787 + 2 ^ n).Prime} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun n hn => C125_main.2.2.2 n hn
  rw [he] at hi
  exact hi Set.finite_empty
