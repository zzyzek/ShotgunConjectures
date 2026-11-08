import Mathlib

/-
NT-B31.4 (Mathlib). Guy B31, Ruderman: for every pair (p, q) of nonnegative integers is
there a positive integer n with n! (n+q)! ∣ (2n - p)! ?

The factorial (2n - p)! needs 2n ≥ p; in ℕ, truncated subtraction would make the
question trivially true at n = 1, so `B31_Ruderman` below demands p ≤ 2n explicitly.

Main theorem `B31_4_main`: Ruderman's statement is equivalent to Erdős problem 727
(Erdős, Graham, Ruzsa, Straus) in the form stated in google-deepmind/formal-conjectures,
  ∀ k ≥ 2, Set.Infinite {n : ℕ | ((n+k)!)^2 ∣ (2n)!}.
Intermediate equivalent `E727weak`: ∀ k, ∃ n, ((n+k)!)^2 ∣ (2n)! (one n for each k).

Proof.
* Ruderman → E727weak: take (p, q) = (2k, 0) and shift n by k.
* E727weak → Ruderman: given (p, q) take k = p + q + 2 and a solution n of E(k);
  then m = n + p + 2 works, since m! (m+q)! ∣ ((n+k)!)^2 ∣ (2n)! ∣ (2m - p)!.
* E727weak → infinitely many: a solution n of E(k') has no prime in (n, n+k'], because
  such a prime ℓ satisfies ℓ² ∣ ((n+k')!)² but ℓ² ∤ (2n)! (as ℓ ≤ 2n < 2ℓ and 2n < ℓ²).
  By Bertrand this forces n ≥ k', and a solution of E(k') is a solution of E(k) for k ≤ k'.

Checked by Lean: everything above. Mathlib inputs: Bertrand's postulate
`Nat.exists_prime_lt_and_le_two_mul`, `Nat.Prime.pow_dvd_factorial_iff`.
Not checked by Lean: nothing; Erdős 727 itself is open, so this settles neither statement.
-/

open Nat

/-- Ruderman's question, with the side condition p ≤ 2n making (2n - p)! meaningful. -/
def B31_Ruderman : Prop :=
  ∀ p q : ℕ, ∃ n : ℕ, 0 < n ∧ p ≤ 2 * n ∧ n ! * (n + q) ! ∣ (2 * n - p) !

/-- Erdős 727, as in formal-conjectures `Erdos727.erdos_727`. -/
def B31_Erdos727 : Prop :=
  ∀ k ≥ 2, Set.Infinite {n : ℕ | ((n + k) !) ^ 2 ∣ (2 * n) !}

/-- One solution for every k. -/
def B31_E727weak : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, ((n + k) !) ^ 2 ∣ (2 * n) !

theorem B31_ruderman_to_weak (h : B31_Ruderman) : B31_E727weak := by
  intro k
  obtain ⟨n, -, hp, hd⟩ := h (2 * k) 0
  refine ⟨n - k, ?_⟩
  have e1 : n - k + k = n := by omega
  have e2 : 2 * (n - k) = 2 * n - 2 * k := by omega
  rw [e1, e2, sq]
  simpa using hd

theorem B31_weak_to_ruderman (h : B31_E727weak) : B31_Ruderman := by
  intro p q
  obtain ⟨n, hn⟩ := h (p + q + 2)
  refine ⟨n + p + 2, by omega, by omega, ?_⟩
  have h1 : (n + p + 2) ! * (n + p + 2 + q) ! ∣ ((n + (p + q + 2)) !) ^ 2 := by
    rw [sq]
    have e : n + p + 2 + q = n + (p + q + 2) := by omega
    rw [e]
    exact Nat.mul_dvd_mul_right (Nat.factorial_dvd_factorial (by omega)) _
  have h2 : (2 * n) ! ∣ (2 * (n + p + 2) - p) ! :=
    Nat.factorial_dvd_factorial (by omega)
  exact h1.trans (hn.trans h2)

/-- A prime ℓ with n < ℓ ≤ 2n has ℓ² ∤ (2n)!. -/
theorem B31_sq_not_dvd (n ℓ : ℕ) (hℓ : ℓ.Prime) (h1 : n < ℓ) (h2 : ℓ ≤ 2 * n) :
    ¬ ℓ ^ 2 ∣ (2 * n) ! := by
  have hn : 1 ≤ n := by
    have := hℓ.two_le
    omega
  have hsq : 2 * n < ℓ ^ 2 := by
    have : 2 * n < ℓ * ℓ := by
      calc 2 * n < 2 * ℓ := by omega
        _ ≤ ℓ * ℓ := Nat.mul_le_mul_right _ hℓ.two_le
    simpa [sq] using this
  have hlog : Nat.log ℓ (2 * n) < 2 := Nat.log_lt_of_lt_pow (by omega) hsq
  rw [hℓ.pow_dvd_factorial_iff hlog]
  have hq : 2 * n / ℓ = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  simp [hq]

theorem B31_solution_large (k n : ℕ) (hk : 2 ≤ k) (h : ((n + k) !) ^ 2 ∣ (2 * n) !) :
    k ≤ n := by
  by_contra hlt'
  have hlt : n < k := Nat.lt_of_not_le hlt'
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp at h
    have : 2 ≤ k ! := by
      calc 2 = 2 ! := rfl
        _ ≤ k ! := Nat.factorial_le hk
    have : 2 ≤ k ! ^ 2 := le_trans this (Nat.le_self_pow (by norm_num) _)
    omega
  · obtain ⟨ℓ, hℓ, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
    apply B31_sq_not_dvd n ℓ hℓ h1 h2
    have : ℓ ∣ (n + k) ! := (Nat.Prime.dvd_factorial hℓ).2 (by omega)
    exact (pow_dvd_pow_of_dvd this 2).trans h

theorem B31_weak_to_erdos (h : B31_E727weak) : B31_Erdos727 := by
  intro k hk
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn⟩ := h (k + a + 1)
  have hbig := B31_solution_large (k + a + 1) n (by omega) hn
  refine ⟨n, ?_, by omega⟩
  simp only [Set.mem_ofPred_eq]
  exact (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) 2).trans hn

theorem B31_erdos_to_weak (h : B31_Erdos727) : B31_E727weak := by
  intro k
  obtain ⟨n, hn⟩ := (h (k + 2) (by omega)).nonempty
  refine ⟨n, ?_⟩
  have hn' : ((n + (k + 2)) !) ^ 2 ∣ (2 * n) ! := hn
  exact (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) 2).trans hn'

theorem B31_4_main : B31_Ruderman ↔ B31_Erdos727 :=
  ⟨fun h => B31_weak_to_erdos (B31_ruderman_to_weak h),
   fun h => B31_weak_to_ruderman (B31_erdos_to_weak h)⟩

theorem B31_4_weak : B31_Ruderman ↔ B31_E727weak :=
  ⟨B31_ruderman_to_weak, B31_weak_to_ruderman⟩

