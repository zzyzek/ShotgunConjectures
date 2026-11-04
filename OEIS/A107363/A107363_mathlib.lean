import Mathlib

/-
OEIS A107363 (Mathlib): expansion of (1-x)(1+x)^2(1+x^2)(1-x^2+2x^3+x^4) /
((1-x^2-x^4)(1+x^2+2x^4-x^6+x^8)). Conjectures (C. Dement, 2005):
{Fib(n)} = {a(n) : a(n) ≥ 0} = {a(n) : n ≢ 2 (mod 6)} (n ≥ 0). README result: true, and
a(6j+2) = -L(3j+1).

Main theorem `A107363_main`: with `A107363_num`, `A107363_den` the numerator and denominator
above in ℤ⟦X⟧ (Mathlib `PowerSeries`), for every c : ℕ → ℤ with mk c * den = num (i.e. c(n)
is the n-th coefficient of num/den; such c exists, `A107363_gf`):
* c n ≥ 0 iff n % 6 ≠ 2;
* {c n | c n ≥ 0} = {c n | n % 6 ≠ 2} = {Nat.fib i | i : ℕ} (as subsets of ℤ);
* c (6j+2) = -(Nat.fib (3j) + Nat.fib (3j+2)) = -L(3j+1) (Lucas number).

Proof. The core part (restated from A107363.lean): a sequence `A107363_a` defined by
a(n+12) = 4a(n+6) + a(n) with 12 initial values, its six 6-sections in terms of Fibonacci
and Lucas numbers, and the set statements. New here: den = 1 - 4X^6 - X^12 and the
coefficient identity mk a * den = num (`A107363_gf`, n < 12 by evaluation, n ≥ 12 by the
recurrence); any c with mk c * den = num equals a, since den has an inverse
(`PowerSeries.mul_invOfUnit`, constant coefficient 1); and the core Fibonacci sequence equals
`Nat.fib`.

Outside Lean: nothing.
-/

open PowerSeries

def A107363_a : Nat → Int
  | 0 => 1 | 1 => 1 | 2 => -1 | 3 => 1 | 4 => 2 | 5 => 0
  | 6 => 5 | 7 => 3 | 8 => -7 | 9 => 3 | 10 => 8 | 11 => 0
  | n + 12 => 4 * A107363_a (n + 6) + A107363_a n

def A107363_F : Nat → Int
  | 0 => 0 | 1 => 1
  | n + 2 => A107363_F (n + 1) + A107363_F n

def A107363_L : Nat → Int
  | 0 => 2 | 1 => 1
  | n + 2 => A107363_L (n + 1) + A107363_L n

theorem A107363_a_rec (n : Nat) : A107363_a (n + 12) = 4 * A107363_a (n + 6) + A107363_a n := by simp only [A107363_a]
theorem A107363_F_rec (n : Nat) : A107363_F (n + 2) = A107363_F (n + 1) + A107363_F n := by simp only [A107363_F]
theorem A107363_L_rec (n : Nat) : A107363_L (n + 2) = A107363_L (n + 1) + A107363_L n := by simp only [A107363_L]

theorem A107363_F_six (k : Nat) : A107363_F (k + 6) = 4 * A107363_F (k + 3) + A107363_F k := by
  have h2 : A107363_F (k + 2) = A107363_F (k + 1) + A107363_F k := A107363_F_rec k
  have h3 : A107363_F (k + 3) = A107363_F (k + 2) + A107363_F (k + 1) := A107363_F_rec (k + 1)
  have h4 : A107363_F (k + 4) = A107363_F (k + 3) + A107363_F (k + 2) := A107363_F_rec (k + 2)
  have h5 : A107363_F (k + 5) = A107363_F (k + 4) + A107363_F (k + 3) := A107363_F_rec (k + 3)
  have h6 : A107363_F (k + 6) = A107363_F (k + 5) + A107363_F (k + 4) := A107363_F_rec (k + 4)
  omega

theorem A107363_L_six (k : Nat) : A107363_L (k + 6) = 4 * A107363_L (k + 3) + A107363_L k := by
  have h2 : A107363_L (k + 2) = A107363_L (k + 1) + A107363_L k := A107363_L_rec k
  have h3 : A107363_L (k + 3) = A107363_L (k + 2) + A107363_L (k + 1) := A107363_L_rec (k + 1)
  have h4 : A107363_L (k + 4) = A107363_L (k + 3) + A107363_L (k + 2) := A107363_L_rec (k + 2)
  have h5 : A107363_L (k + 5) = A107363_L (k + 4) + A107363_L (k + 3) := A107363_L_rec (k + 3)
  have h6 : A107363_L (k + 6) = A107363_L (k + 5) + A107363_L (k + 4) := A107363_L_rec (k + 4)
  omega

theorem A107363_F_nonneg : ∀ n, 0 ≤ A107363_F n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by rw [A107363_F_rec]; have := A107363_F_nonneg (n + 1); have := A107363_F_nonneg n; omega

theorem A107363_L_pos : ∀ n, 0 < A107363_L n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by rw [A107363_L_rec]; have := A107363_L_pos (n + 1); have := A107363_L_pos n; omega

def A107363_S (j : Nat) : Prop :=
  A107363_a (6 * j) = A107363_F (3 * j + 2) ∧ A107363_a (6 * j + 1) = A107363_F (3 * j + 1) ∧ A107363_a (6 * j + 2) = -A107363_L (3 * j + 1) ∧
  A107363_a (6 * j + 3) = A107363_F (3 * j + 1) ∧ A107363_a (6 * j + 4) = A107363_F (3 * j + 3) ∧ A107363_a (6 * j + 5) = 0

theorem A107363_sections : ∀ j, A107363_S j
  | 0 => by unfold A107363_S; decide
  | 1 => by unfold A107363_S; decide
  | j + 2 => by
    have h1 := A107363_sections (j + 1)
    have h0 := A107363_sections j
    unfold A107363_S at *
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h1
    obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h0
    have r : ∀ r, A107363_a (6 * (j + 2) + r) = 4 * A107363_a (6 * (j + 1) + r) + A107363_a (6 * j + r) := by
      intro r
      rw [show 6 * (j + 2) + r = (6 * j + r) + 12 by omega,
          show 6 * (j + 1) + r = (6 * j + r) + 6 by omega]
      exact A107363_a_rec (6 * j + r)
    have f : ∀ c, A107363_F (3 * (j + 2) + c) = 4 * A107363_F (3 * (j + 1) + c) + A107363_F (3 * j + c) := by
      intro c
      rw [show 3 * (j + 2) + c = (3 * j + c) + 6 by omega,
          show 3 * (j + 1) + c = (3 * j + c) + 3 by omega]
      exact A107363_F_six (3 * j + c)
    have l : ∀ c, A107363_L (3 * (j + 2) + c) = 4 * A107363_L (3 * (j + 1) + c) + A107363_L (3 * j + c) := by
      intro c
      rw [show 3 * (j + 2) + c = (3 * j + c) + 6 by omega,
          show 3 * (j + 1) + c = (3 * j + c) + 3 by omega]
      exact A107363_L_six (3 * j + c)
    have r0 := r 0; have r1 := r 1; have r2 := r 2; have r3 := r 3; have r4 := r 4; have r5 := r 5
    have f1 := f 1; have f2 := f 2; have f3 := f 3; have l1 := l 1
    simp only [Nat.add_zero] at r0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem A107363_nonneg_iff (n : Nat) : 0 ≤ A107363_a n ↔ n % 6 ≠ 2 := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := A107363_sections (n / 6)
  have hn : n = 6 * (n / 6) + n % 6 := by omega
  have := A107363_F_nonneg (3 * (n / 6) + 2); have := A107363_F_nonneg (3 * (n / 6) + 1)
  have := A107363_F_nonneg (3 * (n / 6) + 3); have := A107363_L_pos (3 * (n / 6) + 1)
  have h6 : n % 6 < 6 := Nat.mod_lt _ (by decide)
  generalize n / 6 = q at *
  generalize n % 6 = r at *
  subst hn
  match r, h6 with
  | 0, _ => simp only [Nat.add_zero]; omega
  | 1, _ => omega | 2, _ => omega | 3, _ => omega | 4, _ => omega | 5, _ => omega

theorem A107363_fib_of (n : Nat) (h : n % 6 ≠ 2) : ∃ i, A107363_a n = A107363_F i := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := A107363_sections (n / 6)
  have hn : n = 6 * (n / 6) + n % 6 := by omega
  have h6 : n % 6 < 6 := Nat.mod_lt _ (by decide)
  generalize n / 6 = q at *
  generalize n % 6 = r at *
  subst hn
  match r, h6 with
  | 0, _ => exact ⟨_, a0⟩
  | 1, _ => exact ⟨_, a1⟩
  | 2, _ => exact absurd rfl h
  | 3, _ => exact ⟨_, a3⟩
  | 4, _ => exact ⟨_, a4⟩
  | 5, _ => exact ⟨0, by rw [a5]; decide⟩

theorem A107363_all_fib (i : Nat) : ∃ n, n % 6 ≠ 2 ∧ A107363_a n = A107363_F i := by
  obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, i = 3 * q ∨ i = 3 * q + 1 ∨ i = 3 * q + 2 := ⟨i / 3, by omega⟩
  · cases q with
    | zero => exact ⟨5, by decide, by decide⟩
    | succ q =>
      refine ⟨6 * q + 4, by omega, ?_⟩
      rw [(A107363_sections q).2.2.2.2.1, show 3 * (q + 1) = 3 * q + 3 by omega]
  · exact ⟨6 * q + 1, by omega, (A107363_sections q).2.1⟩
  · exact ⟨6 * q, by omega, (A107363_sections q).1⟩

/-! ### The generating function -/

noncomputable def A107363_num : ℤ⟦X⟧ := (1 - X) * (1 + X) ^ 2 * (1 + X ^ 2) * (1 - X ^ 2 + 2 * X ^ 3 + X ^ 4)

noncomputable def A107363_den : ℤ⟦X⟧ := (1 - X ^ 2 - X ^ 4) * (1 + X ^ 2 + 2 * X ^ 4 - X ^ 6 + X ^ 8)

theorem A107363_den_eq : A107363_den = 1 - (X ^ 6 + X ^ 6 + X ^ 6 + X ^ 6) - X ^ 12 := by
  unfold A107363_den; ring

theorem A107363_num_eq : A107363_num = 1 + X - X ^ 2 + X ^ 3 + (X ^ 4 + X ^ 4) + X ^ 6 - X ^ 7 -
    (X ^ 8 + X ^ 8 + X ^ 8) - X ^ 9 := by
  unfold A107363_num; ring

theorem A107363_gf : PowerSeries.mk A107363_a * A107363_den = A107363_num := by
  rw [A107363_den_eq, A107363_num_eq]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mul_X_pow', coeff_mk,
    coeff_one, coeff_X, coeff_X_pow]
  rcases Nat.lt_or_ge n 12 with h | h
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    simp only [show 6 ≤ m + 12 by omega, show 12 ≤ m + 12 by omega, ite_true,
      show m + 12 - 6 = m + 6 by omega, show m + 12 - 12 = m by omega]
    rw [A107363_a_rec]
    simp only [show m + 12 ≠ 0 by omega, show m + 12 ≠ 1 by omega, show m + 12 ≠ 2 by omega,
      show m + 12 ≠ 3 by omega, show m + 12 ≠ 4 by omega, show m + 12 ≠ 6 by omega,
      show m + 12 ≠ 7 by omega, show m + 12 ≠ 8 by omega, show m + 12 ≠ 9 by omega,
      ite_false]
    ring

theorem A107363_unique (c : ℕ → ℤ) (hc : PowerSeries.mk c * A107363_den = A107363_num) :
    c = A107363_a := by
  have hcc : constantCoeff A107363_den = ((1 : ℤˣ) : ℤ) := by
    simp [A107363_den]
  have hinv := PowerSeries.mul_invOfUnit A107363_den 1 hcc
  have h1 : PowerSeries.mk c = PowerSeries.mk A107363_a := by
    have e1 : PowerSeries.mk c = PowerSeries.mk c * A107363_den * invOfUnit A107363_den 1 := by
      rw [mul_assoc, hinv, mul_one]
    have e2 : PowerSeries.mk A107363_a =
        PowerSeries.mk A107363_a * A107363_den * invOfUnit A107363_den 1 := by
      rw [mul_assoc, hinv, mul_one]
    rw [e1, e2, hc, A107363_gf]
  funext n
  have := congrArg (coeff n) h1
  simpa using this

theorem A107363_F_fib : ∀ n, A107363_F n = (Nat.fib n : ℤ)
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    rw [A107363_F_rec, A107363_F_fib (n + 1), A107363_F_fib n, Nat.fib_add_two]
    push_cast; ring

theorem A107363_main (c : ℕ → ℤ) (hc : PowerSeries.mk c * A107363_den = A107363_num) :
    (∀ n, 0 ≤ c n ↔ n % 6 ≠ 2) ∧
    {v : ℤ | ∃ n, c n = v ∧ 0 ≤ c n} = Set.range (fun i => (Nat.fib i : ℤ)) ∧
    {v : ℤ | ∃ n, c n = v ∧ n % 6 ≠ 2} = Set.range (fun i => (Nat.fib i : ℤ)) ∧
    (∀ j, c (6 * j + 2) = -((Nat.fib (3 * j) : ℤ) + Nat.fib (3 * j + 2))) := by
  have hca := A107363_unique c hc
  subst hca
  have h2 : {v : ℤ | ∃ n, A107363_a n = v ∧ n % 6 ≠ 2} =
      Set.range (fun i => (Nat.fib i : ℤ)) := by
    ext v
    simp only [Set.mem_range]
    constructor
    · rintro ⟨n, rfl, hn⟩
      obtain ⟨i, hi⟩ := A107363_fib_of n hn
      exact ⟨i, by rw [hi, A107363_F_fib]⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨n, hn, he⟩ := A107363_all_fib i
      exact ⟨n, by rw [he, A107363_F_fib], hn⟩
  refine ⟨A107363_nonneg_iff, ?_, h2, ?_⟩
  · rw [← h2]
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h, hn⟩; exact ⟨n, h, (A107363_nonneg_iff n).mp hn⟩
    · rintro ⟨n, h, hn⟩; exact ⟨n, h, (A107363_nonneg_iff n).mpr hn⟩
  · intro j
    rw [(A107363_sections j).2.2.1]
    -- L(k+1) = F(k) + F(k+2).
    --
    have hL : ∀ k, A107363_L (k + 1) = A107363_F k + A107363_F (k + 2) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        match k, ih with
        | 0, _ => decide
        | 1, _ => decide
        | k + 2, ih =>
          rw [A107363_L_rec, ih (k + 1) (by omega), ih k (by omega), A107363_F_rec (k + 2),
            A107363_F_rec (k + 1), A107363_F_rec k]
          ring
    rw [hL, A107363_F_fib, A107363_F_fib]
