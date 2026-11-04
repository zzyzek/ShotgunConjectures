import OpenProblemsLib

/-
COM-C032 (Mathlib). Coman, conjecture 32: the Poulet numbers divisible by a smaller Poulet
number and not of the form p((m+1)p - m)((n+1)p - n) are exactly the multiples
5461(42k - 13). README result: false, P = 3048841 = 61 · 151 · 331.

Main theorem `C032_main`: P = 3048841 is a Poulet number (Mathlib `Nat.FermatPsp P 2`), the
smaller Poulet number 49981 divides it, P is not of the form p((m+1)p - m)((n+1)p - n) for
ANY natural numbers p, m, n (not only primes p, so the README's reading "p is a prime factor"
is not needed), and 5461 ∤ P, so P is no 5461(42k - 13). `C032_false` states the
negation of the conjecture's "only if" direction.
Proof of "not of the form": with p = q + 1 the factors are mq + q + 1 ≥ p, so p³ ≤ P,
p ≤ 145 and p ∣ P; the only such p > 1 is 61, and 49981 = (60m + 61)(60n + 61) has no
solution (m ≤ 12, case split).

Outside Lean: nothing.
-/

open OpenProblemsLib

/-- Coman's form p((m+1)p - m)((n+1)p - n) with p, m, n natural numbers. -/
def ComanForm (P : ℕ) : Prop := ∃ p m n : ℕ, P = p * ((m + 1) * p - m) * ((n + 1) * p - n)

theorem poulet_P : Nat.FermatPsp 3048841 2 := fermatPsp_of_pspCheck _ _ 61 (by decide +kernel)

theorem poulet_Q : Nat.FermatPsp 49981 2 := fermatPsp_of_pspCheck _ _ 151 (by decide +kernel)

theorem not_form : ¬ ComanForm 3048841 := by
  rintro ⟨p, m, n, h⟩
  rcases p with _ | q
  · simp at h
  have e1 : (m + 1) * (q + 1) - m = m * q + q + 1 := by
    have : (m + 1) * (q + 1) = m * q + q + 1 + m := by ring
    omega
  have e2 : (n + 1) * (q + 1) - n = n * q + q + 1 := by
    have : (n + 1) * (q + 1) = n * q + q + 1 + n := by ring
    omega
  rw [e1, e2] at h
  have hd : (q + 1) ∣ 3048841 := ⟨(m * q + q + 1) * (n * q + q + 1), by rw [h]; ring⟩
  have hb : q ≤ 144 := by
    by_contra hc
    have h1 : q + 1 ≤ m * q + q + 1 := by omega
    have h2 : q + 1 ≤ n * q + q + 1 := by omega
    have h3 : (q + 1) * (q + 1) * (q + 1) ≤ (q + 1) * (m * q + q + 1) * (n * q + q + 1) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h2
    nlinarith
  interval_cases q <;> norm_num at hd
  · omega
  · have h' : 49981 = (m * 60 + 61) * (n * 60 + 61) := by
      have : 3048841 = 61 * ((m * 60 + 61) * (n * 60 + 61)) := by rw [h]; ring
      omega
    have hm : m ≤ 12 := by nlinarith
    interval_cases m <;> omega

theorem C032_main :
    Nat.FermatPsp 3048841 2 ∧ Nat.FermatPsp 49981 2 ∧ 49981 < 3048841 ∧ 49981 ∣ 3048841 ∧
      ¬ ComanForm 3048841 ∧ ¬ 5461 ∣ 3048841 :=
  ⟨poulet_P, poulet_Q, by norm_num, by norm_num, not_form, by norm_num⟩

/-- The conjecture fails: a Poulet number divisible by a smaller Poulet number, not of
Coman's form, that is not 5461(42k - 13) for any k. -/
theorem C032_false :
    ¬ ∀ P : ℕ, (Nat.FermatPsp P 2 ∧ (∃ Q, Nat.FermatPsp Q 2 ∧ Q < P ∧ Q ∣ P) ∧ ¬ ComanForm P) →
      ∃ k : ℕ, P = 5461 * (42 * k - 13) := by
  intro h
  obtain ⟨k, hk⟩ := h 3048841 ⟨poulet_P, ⟨49981, poulet_Q, by norm_num, by norm_num⟩, not_form⟩
  have : 5461 ∣ 3048841 := ⟨_, hk⟩
  norm_num at this
