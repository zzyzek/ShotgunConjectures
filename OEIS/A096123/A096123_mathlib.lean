import Mathlib

/-
OEIS-A096123 (Mathlib). A096123: least product n*(n-1)*...*(n-k+1) divisible by (n-k)!.
Conjecture (Amarnath Murthy, in the entry): a(n) = n!/(p-1)! for all sufficiently large n,
where p is the least prime with n <= 2p.

Definition used: a(n) = n.descFactorial k for the least k with (n-k)! ∣ n.descFactorial k
(k = n always qualifies). This reproduces the data (checked in certificate/check.gp).

Main theorem `A096123_main`: the conjecture is false. For every prime p and n = 2p the
least prime q with n <= 2q is p, and a(2p) <= (2p)!/p! < (2p)!/(p-1)!, because k = p
qualifies: p! * p! ∣ (2p)!. Since there are infinitely many primes, the conjecture fails
for arbitrarily large n.

Checked: everything above. Not checked here: that the definition matches the entry's
PARI program and data (certificate/check.gp, read-the-definition step).
-/

/-- `A096123 n`: the least product `n (n-1) ... (n-k+1)` divisible by `(n-k)!`. -/
noncomputable def A096123 (n : ℕ) : ℕ :=
  n.descFactorial
    (Nat.find (⟨n, by simp⟩ : ∃ k, (n - k).factorial ∣ n.descFactorial k))

lemma descFactorial_mono (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ n) :
    n.descFactorial k ≤ n.descFactorial l := by
  induction l with
  | zero => simp_all
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le hkl with h | h
    · rw [h]
    · rw [Nat.descFactorial_succ]
      have h1 := ih (by omega) (by omega)
      have h2 : 1 ≤ n - l := by omega
      calc n.descFactorial k ≤ n.descFactorial l := h1
        _ ≤ (n - l) * n.descFactorial l := Nat.le_mul_of_pos_left _ h2

lemma qualifies (p : ℕ) : (2 * p - p).factorial ∣ (2 * p).descFactorial p := by
  have h2 : 2 * p - p = p := by omega
  have hfd := Nat.factorial_mul_descFactorial (show p ≤ 2 * p by omega)
  rw [h2] at hfd ⊢
  have hd : p.factorial * p.factorial ∣ (2 * p).factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add p p
    rwa [show p + p = 2 * p by omega] at this
  rw [← hfd] at hd
  exact (Nat.mul_dvd_mul_iff_left (Nat.factorial_pos p)).mp hd

lemma a_le (p : ℕ) : A096123 (2 * p) ≤ (2 * p).descFactorial p := by
  unfold A096123
  apply descFactorial_mono _ _ (by omega)
  exact Nat.find_min' _ (qualifies p)

lemma target_eq (p : ℕ) (hp : 1 ≤ p) :
    (2 * p).factorial / (p - 1).factorial = (2 * p).descFactorial (p + 1) := by
  have hfd := Nat.factorial_mul_descFactorial (show p + 1 ≤ 2 * p by omega)
  rw [show 2 * p - (p + 1) = p - 1 by omega] at hfd
  rw [← hfd, Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]

theorem A096123_at_double_prime (p : ℕ) (hp : p.Prime) :
    A096123 (2 * p) < (2 * p).factorial / (p - 1).factorial := by
  have h2 := hp.two_le
  rw [target_eq p (by omega), Nat.descFactorial_succ, show 2 * p - p = p by omega]
  have hpos : 0 < (2 * p).descFactorial p := Nat.descFactorial_pos.mpr (by omega)
  calc A096123 (2 * p) ≤ (2 * p).descFactorial p := a_le p
    _ < p * (2 * p).descFactorial p := by nlinarith

/-- The conjecture fails for arbitrarily large `n`: whatever prime `q` is the least prime
with `n ≤ 2q`, `a(n) ≠ n!/(q-1)!`. -/
theorem A096123_main :
    ∀ N : ℕ, ∃ n ≥ N, ∀ q : ℕ, q.Prime → n ≤ 2 * q →
      (∀ r : ℕ, r.Prime → n ≤ 2 * r → q ≤ r) →
      A096123 n ≠ n.factorial / (q - 1).factorial := by
  intro N
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  refine ⟨2 * p, by omega, fun q hq hnq hmin => ?_⟩
  have hqp : q = p := le_antisymm (hmin p hp le_rfl) (by omega)
  subst hqp
  exact (A096123_at_double_prime q hq).ne

/-- The conjecture as a statement, negated. -/
theorem A096123_conjecture_false :
    ¬ ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ, q.Prime → n ≤ 2 * q →
      (∀ r : ℕ, r.Prime → n ≤ 2 * r → q ≤ r) →
      A096123 n = n.factorial / (q - 1).factorial := by
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, h⟩ := A096123_main N
  obtain ⟨q, hqmin, hq⟩ : ∃ q, (∀ r : ℕ, r.Prime → n ≤ 2 * r → q ≤ r) ∧ (q.Prime ∧ n ≤ 2 * q) := by
    obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes n
    classical
    let P : ℕ → Prop := fun q => q.Prime ∧ n ≤ 2 * q
    have hex : ∃ q, P q := ⟨p, hp, by omega⟩
    exact ⟨Nat.find hex, fun r hr hnr => Nat.find_min' hex ⟨hr, hnr⟩, Nat.find_spec hex⟩
  exact h q hq.1 hq.2 hqmin (hN n hn q hq.1 hq.2 hqmin)
