/-
NT-F6.3 (Guy F6 / Erdős #436): is Λ(k,3) finite for odd k ≥ 5?  By Chebotarev and compactness,
Λ(k,3) = ∞ iff some completely additive f : ℕ⁺ → ℤ/k (the "k-th power class" of each n) has
no r ≥ 1 with f(r) = f(r+1) = f(r+2) = 0.  For even k the Lehmers' examples of Λ(k,3) = ∞
are of "character type": f depends only on n mod Q for n prime to Q.

Checked here (core Lean, no Mathlib), values of f read mod k:
* `unit_periodic_has_triple`: for odd k, no f of character type avoids three consecutive
  zeros: r = Q^k - 1 always works (f(Q^k ± 1) = f(±1) = 0 since 2 f(Q-1) = 0 in ℤ/k,
  and f(Q^k) = k f(Q) = 0).  "Prime to Q" is expressed as "invertible mod Q".
Not checked here: the reduction from Λ(k,3) to additive functions (Chebotarev density in
Kummer extensions, compactness) and the SAT witness for Λ(5,3) ≥ 399999 (see README.md).
-/

theorem mod_two_mul_zero (k x : Nat) (hk : k % 2 = 1) (h : (2 * x) % k = 0) : x % k = 0 := by
  have hk1 : (k + 1) % 2 = 0 := by omega
  have e : (k + 1) / 2 * (2 * x) = k * x + x := by
    have : (k + 1) / 2 * 2 = k + 1 := by omega
    calc (k + 1) / 2 * (2 * x) = ((k + 1) / 2 * 2) * x := by rw [Nat.mul_assoc]
      _ = (k + 1) * x := by rw [this]
      _ = k * x + x := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : ((k + 1) / 2 * (2 * x)) % k = 0 := by
    rw [Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]
  rw [e, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod] at h2
  exact h2

theorem one_le_pow_of_one_le {Q : Nat} (j : Nat) (hQ : 1 ≤ Q) : 1 ≤ Q ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ]; exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ hQ)

theorem f_pow (k : Nat) (f : Nat → Nat)
    (hmul : ∀ a b, 1 ≤ a → 1 ≤ b → f (a * b) % k = (f a + f b) % k)
    (Q : Nat) (hQ : 1 ≤ Q) (hf1 : f 1 % k = 0) :
    ∀ j, f (Q ^ j) % k = (j * f Q) % k := by
  intro j
  induction j with
  | zero => simp [hf1]
  | succ j ih =>
    have hpos : 1 ≤ Q ^ j := one_le_pow_of_one_le j hQ
    rw [Nat.pow_succ, hmul _ _ hpos hQ, Nat.add_mod, ih, ← Nat.add_mod, Nat.succ_mul]

theorem unit_periodic_has_triple (k Q : Nat) (hk : k % 2 = 1) (hQ : 2 ≤ Q)
    (f : Nat → Nat) (hf1 : f 1 % k = 0)
    (hmul : ∀ a b, 1 ≤ a → 1 ≤ b → f (a * b) % k = (f a + f b) % k)
    (hper : ∀ a b, (∃ u, (a * u) % Q = 1) → a % Q = b % Q → f a % k = f b % k) :
    ∃ r, 1 ≤ r ∧ f r % k = 0 ∧ f (r + 1) % k = 0 ∧ f (r + 2) % k = 0 := by
  have hQ1 : 1 ≤ Q := by omega
  -- Q^k ≥ Q ≥ 2
  have hpow : Q ≤ Q ^ k := by
    have hk1 : 1 ≤ k := by omega
    calc Q = Q ^ 1 := (Nat.pow_one Q).symm
      _ ≤ Q ^ k := Nat.pow_le_pow_right hQ1 hk1
  -- (Q^k) % Q = 0
  have hmod0 : Q ^ k % Q = 0 := by
    have hk1 : k = (k - 1) + 1 := by omega
    rw [hk1, Nat.pow_succ, Nat.mul_mod_left]
  -- f(Q - 1) = 0, from (Q-1)^2 ≡ 1 (mod Q)
  have hsq : ((Q - 1) * (Q - 1)) % Q = 1 % Q := by
    have : (Q - 1) * (Q - 1) = Q * (Q - 2) + 1 := by
      have e : Q = (Q - 2) + 2 := by omega
      rw [e]; simp only [Nat.add_sub_cancel]
      rw [show Q - 2 + 2 - 1 = (Q - 2) + 1 by omega]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega
    rw [this, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
  have h1unit : ∃ u, (1 * u) % Q = 1 := ⟨1, by rw [Nat.one_mul, Nat.mod_eq_of_lt (by omega)]⟩
  have hfsq : f ((Q - 1) * (Q - 1)) % k = 0 := by
    rw [← hper 1 _ h1unit (by rw [hsq])]; exact hf1
  have hfm1 : f (Q - 1) % k = 0 := by
    rw [hmul _ _ (by omega) (by omega)] at hfsq
    apply mod_two_mul_zero k _ hk
    rw [Nat.two_mul]; exact hfsq
  have hunitm1 : ∃ u, ((Q - 1) * u) % Q = 1 := ⟨Q - 1, by rw [hsq, Nat.mod_eq_of_lt (by omega)]⟩
  refine ⟨Q ^ k - 1, by omega, ?_, ?_, ?_⟩
  · -- Q^k - 1 ≡ Q - 1 (mod Q)
    have hm : (Q - 1) % Q = (Q ^ k - 1) % Q := by
      have e : Q ^ k - 1 = (Q ^ k - Q) + (Q - 1) := by omega
      have hd : (Q ^ k - Q) % Q = 0 := by
        have : Q ^ k - Q = Q * (Q ^ k / Q - 1) := by
          have := Nat.div_add_mod (Q ^ k) Q
          rw [hmod0, Nat.add_zero] at this
          rw [Nat.mul_sub, Nat.mul_one]; omega
        rw [this, Nat.mul_mod_right]
      rw [e, Nat.add_mod, hd, Nat.zero_add, Nat.mod_mod]
    rw [← hper _ _ hunitm1 hm]; exact hfm1
  · have e : Q ^ k - 1 + 1 = Q ^ k := by omega
    rw [e, f_pow k f hmul Q hQ1 hf1 k, Nat.mul_mod_right]
  · have e : Q ^ k - 1 + 2 = Q ^ k + 1 := by omega
    have hm : 1 % Q = (Q ^ k + 1) % Q := by
      rw [Nat.add_mod, hmod0, Nat.zero_add, Nat.mod_mod]
    rw [e, ← hper 1 _ h1unit hm]; exact hf1
