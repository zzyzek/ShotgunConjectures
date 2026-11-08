import Mathlib

/-
OEIS A123365 (3 c(n) = n + 2, c(n) = number of cubes mod n), conjecture ladder 2026-11-08, rung R2.

Checked here (Lean + Mathlib):
* `three_cubeCount_ne_two_and_two_odd`: no n = 2^e x^a y^b (x != y odd primes, e, a, b >= 1)
  satisfies 3 c(n) = n + 2, with c = `cubeCount` (cubeCount n = #{x^3 mod n : 0 <= x < n},
  the definition of A046530). No hypotheses.
* `two_mixed`: for primes p = 1, r = 2 (mod 3) with r >= 5 and a, b >= 1,
  (p + 2) c(2^a) c(r^b) != p 2^a r^b + 2, with c(q^e) given by the closed form `cq` (all p at once).
* `three_c_ne_two_and_two_odd`: the same statement for any c satisfying the three properties below.
* the three properties, proved for `cubeCount`:
  `cubeCount_mul` (multiplicative on coprime arguments, by the Chinese remainder theorem),
  `cubeCount_prime_pow_two` (c(q^e) = cq q e for primes q = 2 (mod 3)),
  `cubeCount_prime_pow_one` (3 c(p^e) = 3 + (p - 1) s1(p, e) for primes p = 1 (mod 3)).
  Route: c(p^f) = #(cubes of units mod p^f) + c(p^(f-3)) (`cubeCount_prime_pow_step`: a non-unit
  is p z and its cube is p^3 z^3); the unit cubes number phi(p^f) when 3 does not divide phi(p^f)
  and phi(p^f)/3 when the unit group is cyclic of order divisible by 3.
* helper facts on the closed form: `cq_closed` ((q^2+q+1) c(q^e) = q^(e+2) + q^2+q+1 - q^((e+2) mod 3)),
  `cq_le_pow`, `cq_lower`, `s1_le_pow`, `s1_le_pow_two`.
NOT checked here: nothing beyond reading the definition of `cubeCount` as A046530.
The definitions s1, cq repeat those of A123365_mathlib.lean so that this file stands alone.
-/


def s1 (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => q
  | (e + 3) => q ^ (e + 2) + s1 q e

def cq (q e : ℕ) : ℕ := 1 + (q - 1) * s1 q e

lemma s1_mod (q : ℕ) : ∀ t r, s1 q (3 * t + r) % q = s1 q r % q
  | 0, r => by simp
  | t + 1, r => by
    have ih := s1_mod q t r
    have e1 : 3 * (t + 1) + r = (3 * t + r) + 3 := by ring
    rw [e1]
    show (q ^ (3 * t + r + 2) + s1 q (3 * t + r)) % q = _
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_pow_self q (by omega)), ih]
    simp

lemma s1_two_mul (t : ℕ) : 7 * s1 2 (3 * t + 1) + 1 = 8 ^ (t + 1) := by
  induction t with
  | zero => simp [s1]
  | succ t ih =>
    have e1 : 3 * (t + 1) + 1 = (3 * t + 1) + 3 := by ring
    rw [e1]
    show 7 * (2 ^ (3 * t + 1 + 2) + s1 2 (3 * t + 1)) + 1 = 8 ^ (t + 1 + 1)
    have e2 : (2 : ℕ) ^ (3 * t + 1 + 2) = 8 ^ (t + 1) := by
      rw [show 3 * t + 1 + 2 = 3 * (t + 1) by ring, pow_mul]; norm_num
    rw [e2, pow_succ]; omega

/-- Closed form: (q^3 - 1) s1(q, e) + q^((e + 2) mod 3) = q^(e + 2). -/
lemma s1_closed (q : ℕ) : ∀ e, ((q : ℤ) ^ 3 - 1) * (s1 q e : ℤ) + (q : ℤ) ^ ((e + 2) % 3)
    = (q : ℤ) ^ (e + 2)
  | 0 => by simp [s1]
  | 1 => by simp [s1]
  | 2 => by simp [s1]; ring
  | e + 3 => by
    have ih := s1_closed q e
    have h3 : (e + 3 + 2) % 3 = (e + 2) % 3 := by omega
    rw [h3]
    show ((q : ℤ) ^ 3 - 1) * ((q ^ (e + 2) + s1 q e : ℕ) : ℤ) + _ = _
    push_cast
    have : (q : ℤ) ^ (e + 3 + 2) = (q : ℤ) ^ 3 * (q : ℤ) ^ (e + 2) := by ring
    rw [this]; linear_combination ih

/-- (q^2 + q + 1) c(q^e) = q^(e+2) + (q^2 + q + 1) - q^((e+2) mod 3). -/
lemma cq_closed {q : ℕ} (hq : 1 ≤ q) (e : ℕ) :
    ((q : ℤ) ^ 2 + q + 1) * (cq q e : ℤ)
      = (q : ℤ) ^ (e + 2) + ((q : ℤ) ^ 2 + q + 1) - (q : ℤ) ^ ((e + 2) % 3) := by
  have h := s1_closed q e
  unfold cq
  push_cast [Nat.cast_sub hq]
  linear_combination h

lemma s1_le_pow (q : ℕ) (hq : 1 ≤ q) : ∀ e, s1 q e * (q - 1) + 1 ≤ q ^ e
  | 0 => by simp [s1]
  | 1 => by simp [s1]; omega
  | 2 => by
    simp only [s1]
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith
  | e + 3 => by
    have ih := s1_le_pow q hq e
    show (q ^ (e + 2) + s1 q e) * (q - 1) + 1 ≤ q ^ (e + 3)
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    have : (r + 1) ^ (e + 3) = (r + 1) ^ (e + 2) * (r + 1) := by ring
    rw [this]
    have h1 : 1 ≤ (r + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    have h2 : (r + 1) ^ e ≤ (r + 1) ^ (e + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith

lemma cq_le_pow {q : ℕ} (hq : 1 ≤ q) (e : ℕ) : cq q e ≤ q ^ e := by
  have := s1_le_pow q hq e
  unfold cq; nlinarith [Nat.mul_comm (q - 1) (s1 q e)]

/-- Main lemma (all p): for primes p ≡ 1 and r ≡ 2 (mod 3), r ≥ 5, and a, b ≥ 1,
(p + 2) c(2^a) c(r^b) ≠ p 2^a r^b + 2 (c given by the closed form `cq`). -/
theorem two_mixed {p r a b : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) (hr : r.Prime)
    (hr3 : r % 3 = 2) (hr5 : 5 ≤ r) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (p + 2) * (cq 2 a * cq r b) ≠ p * (2 ^ a * r ^ b) + 2 := by
  intro hE
  have hp7 : 7 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega
  have hpodd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with h | h
    · rcases hp.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.mp h) with h' | h' <;> omega
    · exact Nat.odd_iff.mp h
  have hrodd : r % 2 = 1 := by
    rcases Nat.even_or_odd r with h | h
    · rcases hr.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.mp h) with h' | h' <;> omega
    · exact Nat.odd_iff.mp h
  have hcr : cq r b % 2 = 1 := by
    unfold cq
    have : 2 ∣ r - 1 := by omega
    obtain ⟨k, hk⟩ := this
    rw [hk, mul_assoc, Nat.add_mod, Nat.mul_mod_right]
  -- Step 1: a ≢ 1 (mod 3) contradicts parity.
  by_cases ha3 : a % 3 = 1
  swap
  · have hs : s1 2 a % 2 = 0 := by
      have hd := s1_mod 2 (a / 3) (a % 3)
      have : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
      rw [this] at hd
      rw [hd]
      have : a % 3 = 0 ∨ a % 3 = 2 := by omega
      rcases this with h | h <;> rw [h] <;> simp [s1]
    have hc2 : cq 2 a % 2 = 1 := by unfold cq; omega
    have hL : (p + 2) * (cq 2 a * cq r b) % 2 = 1 := by
      rw [Nat.mul_mod, Nat.mul_mod (cq 2 a), hc2, hcr]; omega
    have hR : (p * (2 ^ a * r ^ b) + 2) % 2 = 0 := by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [pow_succ]
      have : p * (2 ^ a' * 2 * r ^ b) + 2 = 2 * (p * 2 ^ a' * r ^ b + 1) := by ring
      rw [this]; simp
    omega
  obtain ⟨t, rfl⟩ : ∃ t, a = 3 * t + 1 := ⟨a / 3, by omega⟩
  have hs := s1_two_mul t
  have h2a : (2 : ℕ) ^ (3 * t + 1) = 2 * 8 ^ t := by
    rw [pow_succ, pow_mul]; norm_num; ring
  have hcrle := cq_le_pow (show 1 ≤ r by omega) b
  rcases Nat.eq_zero_or_pos t with ht | ht
  swap
  · -- Step 2: a ≥ 4: ratio bound.
    have hu : 8 ≤ 8 ^ t := by
      calc 8 = 8 ^ 1 := by norm_num
        _ ≤ 8 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    have hc2 : 7 * cq 2 (3 * t + 1) = 8 * 8 ^ t + 6 := by
      unfold cq; rw [pow_succ] at hs; simp; omega
    rw [h2a] at hE
    set u := 8 ^ t
    set C := cq 2 (3 * t + 1)
    set D := cq r b
    set Y := r ^ b
    have hY : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
    have k1 : 7 * ((p + 2) * (C * D)) ≤ (p + 2) * (8 * u + 6) * Y := by
      have : 7 * ((p + 2) * (C * D)) = (p + 2) * (7 * C) * D := by ring
      rw [this, hc2]; exact Nat.mul_le_mul_left _ hcrle
    have k2 : (p + 2) * (8 * u + 6) + 1 ≤ 14 * p * u := by nlinarith
    have k3 : ((p + 2) * (8 * u + 6) + 1) * Y ≤ 14 * p * u * Y := Nat.mul_le_mul_right _ k2
    nlinarith
  · -- Step 3: a = 1: (p + 2) c(r^b) = p r^b + 1.
    subst ht
    have hc21 : cq 2 1 = 2 := by simp [cq, s1]
    simp only [Nat.mul_zero, Nat.zero_add, pow_one, hc21] at hE
    have hE1 : (p + 2) * cq r b = p * r ^ b + 1 := by
      have : 2 * ((p + 2) * cq r b) = 2 * (p * r ^ b + 1) := by linarith
      omega
    clear hE hs h2a hcrle hcr hc21 hrodd hp3 hr3
    -- residue of b mod 3
    have hcl := cq_closed (show 1 ≤ r by omega) b
    have hEz : ((p : ℤ) + 2) * (cq r b : ℤ) = (p : ℤ) * (r : ℤ) ^ b + 1 := by exact_mod_cast hE1
    have hpow2 : (r : ℤ) ^ (b + 2) = (r : ℤ) ^ 2 * (r : ℤ) ^ b := by ring
    rcases (show b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 by omega) with h3 | h3 | h3
    · -- b ≡ 0: b ≥ 3, beta = r + 1.
      have hb3 : 3 ≤ b := by omega
      have h32 : (b + 2) % 3 = 2 := by omega
      rw [h32, hpow2] at hcl
      have hY3 : (r : ℤ) ^ 3 ≤ (r : ℤ) ^ b := pow_le_pow_right₀ (by norm_cast; omega) hb3
      have hR5 : (5 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr5
      have hP7 : (7 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp7
      set Y : ℤ := (r : ℤ) ^ b
      set R : ℤ := (r : ℤ)
      set P : ℤ := (p : ℤ)
      -- Y (2R^2 - P(R+1)) = R^2 - (P+1)(R+1)
      have key : Y * (2 * R ^ 2 - P * (R + 1)) = R ^ 2 - (P + 1) * (R + 1) := by
        have h0 : (R ^ 2 + R + 1) * ((P + 2) * (cq r b : ℤ)) = (R ^ 2 + R + 1) * (P * Y + 1) := by
          rw [hEz]
        have e2 : (R ^ 2 + R + 1) * ((P + 2) * (cq r b : ℤ))
            = (P + 2) * (R ^ 2 * Y + (R ^ 2 + R + 1) - R ^ 2) := by
          rw [← hcl]; ring
        have h := e2.symm.trans h0
        linear_combination h
      have hR3 : R ^ 3 ≤ Y := hY3
      clear hcl hEz hpow2 hY3
      have a2 : 5 * R ≤ R ^ 2 := by
        calc 5 * R ≤ R * R := mul_le_mul_of_nonneg_right hR5 (by linarith)
          _ = R ^ 2 := by ring
      have a3 : 5 * R ^ 2 ≤ R ^ 3 := by
        calc 5 * R ^ 2 ≤ R * R ^ 2 := mul_le_mul_of_nonneg_right hR5 (sq_nonneg R)
          _ = R ^ 3 := by ring
      have hR2 : R ^ 2 < R ^ 3 := by linarith
      rcases lt_trichotomy (2 * R ^ 2 - P * (R + 1)) 0 with hl | hl | hl
      · -- μ = P(R+1) - 2R^2 ≥ 1
        have hμ : 1 ≤ P * (R + 1) - 2 * R ^ 2 := by linarith
        have key' : Y * (P * (R + 1) - 2 * R ^ 2) = (P + 1) * (R + 1) - R ^ 2 := by
          linear_combination -key
        have k1 : R ^ 3 * (P * (R + 1) - 2 * R ^ 2) ≤ (P + 1) * (R + 1) - R ^ 2 := by
          rw [← key']; exact mul_le_mul_of_nonneg_right hR3 (by linarith)
        have k0 : R ^ 3 ≤ R ^ 3 * (P * (R + 1) - 2 * R ^ 2) :=
          le_mul_of_one_le_right (by positivity) hμ
        have k2 : R ^ 2 ≤ P + 1 := by
          by_contra hc
          replace hc := not_le.mp hc
          have : (P + 1) * (R + 1) < R ^ 2 * (R + 1) := mul_lt_mul_of_pos_right hc (by linarith)
          linarith
        obtain ⟨K, hK0, hK⟩ : ∃ K : ℤ, 0 ≤ K ∧ P = R ^ 2 - 1 + K := ⟨P - (R ^ 2 - 1), by linarith, by ring⟩
        rw [hK] at k1
        have p1 : 0 ≤ K * ((R + 1) * (R ^ 3 - 1)) :=
          mul_nonneg hK0 (mul_nonneg (by linarith)
            (sub_nonneg.mpr (one_le_pow₀ (show (1:ℤ) ≤ R by linarith))))
        have p2 : 0 < R ^ 3 * (R ^ 3 - R ^ 2 - R - 2) := by
          have : 0 < R ^ 3 - R ^ 2 - R - 2 := by linarith
          positivity
        have e : R ^ 3 * ((R ^ 2 - 1 + K) * (R + 1) - 2 * R ^ 2) - ((R ^ 2 - 1 + K + 1) * (R + 1) - R ^ 2)
            = R ^ 3 * (R ^ 3 - R ^ 2 - R - 2) + K * ((R + 1) * (R ^ 3 - 1)) := by ring
        linarith
      · have k : R ^ 2 - (P + 1) * (R + 1) = 0 := by rw [hl, mul_zero] at key; linarith
        have k' : P * (R + 1) = 2 * R ^ 2 := by linarith
        have : R ^ 2 + R + 1 = 0 := by linear_combination -k - k'
        have : 0 < R ^ 2 + R + 1 := by positivity
        linarith
      · have h1 : 1 ≤ 2 * R ^ 2 - P * (R + 1) := by linarith
        have : Y ≤ Y * (2 * R ^ 2 - P * (R + 1)) := le_mul_of_one_le_right (by positivity) h1
        have : 0 ≤ (P + 1) * (R + 1) := by positivity
        linarith
    · -- b ≡ 1: r ∣ c(r^b), contradiction mod r.
      have hd := s1_mod r (b / 3) (b % 3)
      have : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
      rw [this, h3] at hd
      simp only [s1] at hd
      have hr1 : 1 % r = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hr1] at hd
      have hdiv : r ∣ cq r b := by
        unfold cq
        have e := Nat.div_add_mod (s1 r b) r
        rw [hd] at e
        rw [← e]
        have : 1 + (r - 1) * (r * (s1 r b / r) + 1) = r * (1 + (r - 1) * (s1 r b / r)) := by
          obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
          simp only [Nat.add_sub_cancel]; ring
        rw [this]; exact dvd_mul_right _ _
      have h1 : r ∣ p * r ^ b + 1 := hE1 ▸ dvd_mul_of_dvd_right hdiv _
      have h2 : r ∣ p * r ^ b := dvd_mul_of_dvd_right (dvd_pow_self r (by omega)) _
      have := (Nat.dvd_add_right h2).mp h1
      have := Nat.le_of_dvd (by norm_num) this
      exact absurd (le_trans hr5 this) (by norm_num)
    · -- b ≡ 2: b ≥ 2, beta = r^2 + 1; forces p = 2r - 1, then r^2 ∣ 2r^3 + r.
      have hb2 : 2 ≤ b := by omega
      have h32 : (b + 2) % 3 = 1 := by omega
      rw [h32, hpow2] at hcl
      obtain ⟨Z, hZ⟩ : r ^ 2 ∣ r ^ b := pow_dvd_pow r hb2
      have hZz : (r : ℤ) ^ b = (r : ℤ) ^ 2 * (Z : ℤ) := by exact_mod_cast hZ
      have hR5 : (5 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr5
      have hP7 : (7 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp7
      set R : ℤ := (r : ℤ)
      set P : ℤ := (p : ℤ)
      have hZ1 : (1 : ℤ) ≤ Z := by
        have : 0 < Z := by
          rcases Nat.eq_zero_or_pos Z with h | h
          · rw [h] at hZ; have := pow_pos (show 0 < r by omega) b; omega
          · exact h
        exact_mod_cast this
      have key : R ^ 2 * Z * (P * (R + 1) - 2 * R ^ 2) = (P + 1) * R ^ 2 - R + (P + 1) := by
        have h0 : (R ^ 2 + R + 1) * ((P + 2) * (cq r b : ℤ)) = (R ^ 2 + R + 1) * (P * R ^ b + 1) := by
          rw [hEz]
        rw [hZz] at h0 hcl
        have e2 : (R ^ 2 + R + 1) * ((P + 2) * (cq r b : ℤ))
            = (P + 2) * (R ^ 2 * (R ^ 2 * Z) + (R ^ 2 + R + 1) - R ^ 1) := by
          rw [← hcl]; ring
        have h := e2.symm.trans h0
        linear_combination -h
      clear hcl hEz hpow2 hZz hZ
      have a2 : 5 * R ≤ R ^ 2 := by
        calc 5 * R ≤ R * R := mul_le_mul_of_nonneg_right hR5 (by linarith)
          _ = R ^ 2 := by ring
      have a3 : 5 * R ^ 2 ≤ R ^ 3 := by
        calc 5 * R ^ 2 ≤ R * R ^ 2 := mul_le_mul_of_nonneg_right hR5 (sq_nonneg R)
          _ = R ^ 3 := by ring
      have hPR : 0 ≤ P * R ^ 2 := by positivity
      have hrhs : 0 < (P + 1) * R ^ 2 - R + (P + 1) := by linarith
      have hpos : 1 ≤ P * (R + 1) - 2 * R ^ 2 := by
        by_contra hneg
        replace hneg := not_le.mp hneg
        have : R ^ 2 * Z * (P * (R + 1) - 2 * R ^ 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        linarith
      have hA : R ^ 2 * (P * (R + 1) - 2 * R ^ 2) ≤ (P + 1) * R ^ 2 - R + (P + 1) := by
        rw [← key]
        have := mul_le_mul_of_nonneg_left hZ1
          (show (0:ℤ) ≤ R ^ 2 * (P * (R + 1) - 2 * R ^ 2) by positivity)
        linarith
      have hc3 : R ^ 2 + R + 1 < R ^ 3 - 1 := by linarith
      have hP2 : P ≤ 2 * R := by
        by_contra hc
        replace hc := not_le.mp hc
        have h1 : (2 * R + 1) * (R ^ 3 - 1) ≤ P * (R ^ 3 - 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        linarith
      have hP1 : 2 * R - 1 ≤ P := by
        by_contra hc
        replace hc := not_le.mp hc
        have h1 : P * (R + 1) ≤ (2 * R - 2) * (R + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        linarith
      have hPodd : P ≠ 2 * R := by
        intro h
        have : (p : ℤ) = 2 * r := h
        have : p = 2 * r := by exact_mod_cast this
        omega
      have hPe : P = 2 * R - 1 := by omega
      rw [hPe] at key
      have k3 : R * (R * Z * (R - 1) - (2 * R ^ 2 + 1)) = 0 := by linear_combination key
      have hR0 : R ≠ 0 := by linarith
      have k4 : R * Z * (R - 1) = 2 * R ^ 2 + 1 := by
        have := (mul_eq_zero.mp k3).resolve_left hR0
        linarith
      have : R ∣ 1 := by
        have h1 : R ∣ 2 * R ^ 2 + 1 := ⟨Z * (R - 1), by linarith [k4]⟩
        have h2 : R ∣ 2 * R ^ 2 := ⟨2 * R, by ring⟩
        exact (dvd_add_right h2).mp h1
      have := Int.le_of_dvd (by norm_num) this
      linarith

lemma s1_le_pow_two (q : ℕ) (hq : 1 ≤ q) : ∀ e, 2 ≤ e → s1 q e * (q - 1) + q ≤ q ^ e
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by
    simp only [s1]
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith
  | e + 3, _ => by
    have ih := s1_le_pow q hq e
    show (q ^ (e + 2) + s1 q e) * (q - 1) + q ≤ q ^ (e + 3)
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    have e1 : (r + 1) ^ (e + 3) = (r + 1) ^ (e + 2) * (r + 1) := by ring
    have e2 : (r + 1) ^ (e + 2) = (r + 1) ^ e * (r + 1) ^ 2 := by ring
    rw [e1, e2]
    have h1 : 1 ≤ (r + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    generalize (r + 1) ^ e = W at *
    have h3 : r ≤ W * (r * r + 2 * r) := by
      calc r ≤ 1 * (r * r + 2 * r) := by nlinarith
        _ ≤ W * (r * r + 2 * r) := Nat.mul_le_mul_right _ h1
    nlinarith

/-- For a prime q ≡ 2 (mod 3) and e ≥ 1: q · c(q^e) > (q - 1) q^e. -/
lemma cq_lower {q e : ℕ} (hq : 2 ≤ q) (he : 1 ≤ e) : (q - 1) * q ^ e < q * cq q e := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have h1 := s1_le_pow q (by omega) e'
  -- s1 q (e' + 1) ≥ q ^ e'
  have h0 : q ^ e' ≤ s1 q (e' + 1) := by
    rcases (show e' = 0 ∨ e' = 1 ∨ 2 ≤ e' by omega) with h | h | h
    · subst h; simp [s1]
    · subst h; simp [s1]
    · obtain ⟨k, rfl⟩ : ∃ k, e' = k + 2 := ⟨e' - 2, by omega⟩
      show q ^ (k + 2) ≤ q ^ (k + 2) + s1 q k
      omega
  unfold cq
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have : r * (r + 1) ^ (e' + 1) = r * (r + 1) ^ e' * (r + 1) := by ring
  rw [this]
  have h4 := Nat.mul_le_mul_left (r * (r + 1)) h0
  generalize s1 (r + 1) (e' + 1) = S at *
  generalize (r + 1) ^ e' = W at *
  nlinarith

/-- Corollary: no n with exactly three distinct prime factors, one of them 2, satisfies
3 c(n) = n + 2, assuming c is multiplicative and the closed forms of c at prime powers
(the same three hypotheses as `A123365_mathlib.lean`). -/
theorem three_c_ne_two_and_two_odd (c : ℕ → ℕ)
    (hmul : ∀ m k, Nat.Coprime m k → c (m * k) = c m * c k)
    (h2 : ∀ q e, q.Prime → q % 3 = 2 → c (q ^ e) = cq q e)
    (h1 : ∀ p e, p.Prime → p % 3 = 1 → 3 * c (p ^ e) = 3 + (p - 1) * s1 p e)
    {x y e a b : ℕ} (hx : x.Prime) (hy : y.Prime) (hx2 : x ≠ 2) (hy2 : y ≠ 2) (hxy : x ≠ y)
    (he : 1 ≤ e) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    3 * c (2 ^ e * x ^ a * y ^ b) ≠ 2 ^ e * x ^ a * y ^ b + 2 := by
  intro hE
  have hxg := hx.two_le
  have hyg := hy.two_le
  have c1 : Nat.Coprime (2 ^ e) (x ^ a) :=
    Nat.Coprime.pow e a ((Nat.coprime_primes Nat.prime_two hx).mpr (Ne.symm hx2))
  have c2 : Nat.Coprime (2 ^ e * x ^ a) (y ^ b) := by
    apply Nat.coprime_mul_iff_left.mpr ⟨?_, ?_⟩
    · exact Nat.Coprime.pow e b ((Nat.coprime_primes Nat.prime_two hy).mpr (Ne.symm hy2))
    · exact Nat.Coprime.pow a b ((Nat.coprime_primes hx hy).mpr hxy)
  rw [hmul _ _ c2, hmul _ _ c1, h2 2 e Nat.prime_two (by norm_num)] at hE
  set Z := 2 ^ e
  set X := x ^ a
  set Y := y ^ b
  have hZ2 : 2 ≤ Z := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ Z := Nat.pow_le_pow_right (by norm_num) he
  have hXx : x ≤ X := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ X := Nat.pow_le_pow_right (by omega) ha
  have hYy : y ≤ Y := by
    calc y = y ^ 1 := (pow_one y).symm
      _ ≤ Y := Nat.pow_le_pow_right (by omega) hb
  -- residues: 3 ∤ x, y since n ≡ 1 (mod 3)
  have hn3 : (Z * X * Y) % 3 = 1 := by omega
  have nd3 : ∀ z k, z.Prime → 1 ≤ k → z ^ k ∣ Z * X * Y → z % 3 = 1 ∨ z % 3 = 2 := by
    intro z k hz hk hd
    rcases Nat.lt_or_ge (z % 3) 1 with h | h
    · exfalso
      have : 3 ∣ Z * X * Y := (show 3 ∣ z by omega).trans ((dvd_pow_self z (by omega)).trans hd)
      omega
    · omega
  have rx := nd3 x a hx ha ⟨Z * Y, by simp only [X]; ring⟩
  have ry := nd3 y b hy hb ⟨Z * X, by simp only [Y]; ring⟩
  have hcZ : cq 2 e ≤ Z := cq_le_pow (show 1 ≤ 2 by norm_num) e
  -- bounds for a prime ≡ 1 (mod 3)
  have one_b : ∀ p k, p.Prime → p % 3 = 1 → 1 ≤ k →
      3 * c (p ^ k) ≤ p ^ k + 2 ∧ (2 ≤ k → 3 * c (p ^ k) + 2 ≤ p ^ k) := by
    intro p k hp hp3 hk
    have hp7 : 7 ≤ p := by
      have := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    have hc := h1 p k hp hp3
    have s := s1_le_pow p (by omega) k
    refine ⟨?_, fun hk2 => ?_⟩
    · rw [hc]; nlinarith [Nat.mul_comm (p - 1) (s1 p k)]
    · have s' := s1_le_pow_two p (by omega) k hk2
      rw [hc]; nlinarith [Nat.mul_comm (p - 1) (s1 p k)]
  rcases rx with rx | rx <;> rcases ry with ry | ry
  · -- x, y ≡ 1: 9 c(X) c(Y) ≤ (X + 2)(Y + 2) < 3 X Y.
    have bx : 3 * c X ≤ X + 2 := (one_b x a hx rx ha).1
    have bY : 3 * c Y ≤ Y + 2 := (one_b y b hy ry hb).1
    have hx7 : 7 ≤ X := le_trans (by have h4 : x ≠ 4 := by rintro rfl; norm_num at hx
                                     omega) hXx
    have hy7 : 7 ≤ Y := le_trans (by have h4 : y ≠ 4 := by rintro rfl; norm_num at hy
                                     omega) hYy
    have k1 := Nat.mul_le_mul bx bY
    have k2 : (X + 2) * (Y + 2) + 1 ≤ 3 * (X * Y) := by nlinarith
    have k3 : 3 * (c X * c Y) < X * Y := by linarith
    have k4 : 3 * (cq 2 e * c X * c Y) < Z * X * Y := by
      have : 3 * (cq 2 e * c X * c Y) = cq 2 e * (3 * (c X * c Y)) := by ring
      rw [this]
      calc cq 2 e * (3 * (c X * c Y)) ≤ Z * (3 * (c X * c Y)) := Nat.mul_le_mul_right _ hcZ
        _ < Z * (X * Y) := Nat.mul_lt_mul_of_pos_left k3 (by omega)
        _ = Z * X * Y := by ring
    omega
  · -- x ≡ 1, y ≡ 2
    rw [h2 y b hy ry] at hE
    have hy5 : 5 ≤ y := by omega
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have ha1 : a = 1 := by omega
      have hc := h1 x a hx rx
      rw [ha1] at hc
      simp only [s1, mul_one] at hc
      have hcx : 3 * c X = x + 2 := by simp only [X, ha1]; omega
      apply two_mixed hx rx hy ry hy5 he hb
      have : 3 * (cq 2 e * c X * cq y b) = (3 * c X) * (cq 2 e * cq y b) := by ring
      rw [this, hcx] at hE
      simp only [X, ha1, pow_one] at hE
      rw [hE]; ring
    · have bx : 3 * c X + 2 ≤ X := (one_b x a hx rx ha).2 ha2
      have cyl : cq y b ≤ Y := cq_le_pow (show 1 ≤ y by omega) b
      have : 3 * (cq 2 e * c X * cq y b) ≤ Z * (X - 2) * Y := by
        have e1 : 3 * (cq 2 e * c X * cq y b) = cq 2 e * (3 * c X) * cq y b := by ring
        rw [e1]
        exact Nat.mul_le_mul (Nat.mul_le_mul hcZ (by omega)) cyl
      have : Z * (X - 2) * Y ≤ Z * X * Y := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      omega
  · -- x ≡ 2, y ≡ 1 (symmetric)
    rw [h2 x a hx rx] at hE
    have hx5 : 5 ≤ x := by omega
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · have hb1 : b = 1 := by omega
      have hc := h1 y b hy ry
      rw [hb1] at hc
      simp only [s1, mul_one] at hc
      have hcy : 3 * c Y = y + 2 := by simp only [Y, hb1]; omega
      apply two_mixed hy ry hx rx hx5 he ha
      have : 3 * (cq 2 e * cq x a * c Y) = (3 * c Y) * (cq 2 e * cq x a) := by ring
      rw [this, hcy] at hE
      simp only [Y, hb1, pow_one] at hE
      rw [hE]; ring
    · have bY : 3 * c Y + 2 ≤ Y := (one_b y b hy ry hb).2 hb2
      have cxl : cq x a ≤ X := cq_le_pow (show 1 ≤ x by omega) a
      have : 3 * (cq 2 e * cq x a * c Y) ≤ Z * X * (Y - 2) := by
        have e1 : 3 * (cq 2 e * cq x a * c Y) = cq 2 e * cq x a * (3 * c Y) := by ring
        rw [e1]
        exact Nat.mul_le_mul (Nat.mul_le_mul hcZ cxl) (by omega)
      have : Z * X * (Y - 2) ≤ Z * X * Y := Nat.mul_le_mul_left _ (by omega)
      omega
  · -- all three ≡ 2 (mod 3): 2xy c(n) > (x-1)(y-1) n and 3(x-1)(y-1) ≥ 2xy + 10.
    rw [h2 x a hx rx, h2 y b hy ry] at hE
    have l2 : (2 - 1) * Z < 2 * cq 2 e := cq_lower (show 2 ≤ 2 by norm_num) he
    have lx : (x - 1) * X < x * cq x a := cq_lower hxg ha
    have ly : (y - 1) * Y < y * cq y b := cq_lower hyg hb
    simp only [show (2:ℕ) - 1 = 1 by norm_num, one_mul] at l2
    have hx5 : 5 ≤ x := by omega
    have hy5 : 5 ≤ y := by omega
    have hxy16 : 2 * x * y + 10 ≤ 3 * ((x - 1) * (y - 1)) := by
      have : 11 ≤ x ∨ 11 ≤ y := by
        by_contra h
        push Not at h
        have : x = 5 := by
          have : x ≠ 8 := by rintro rfl; norm_num at hx
          omega
        have : y = 5 := by
          have : y ≠ 8 := by rintro rfl; norm_num at hy
          omega
        omega
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rcases this with h | h <;> nlinarith
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at lx ly hxy16
    set A := cq 2 e
    set B := cq (x' + 1) a
    set C := cq (y' + 1) b
    -- (x' X)(y' Y) Z < (2 A)((x'+1) B)((y'+1) C)
    have m1 : x' * X * (y' * Y) < (x' + 1) * B * ((y' + 1) * C) :=
      Nat.mul_lt_mul'' lx ly
    have m2 : Z * (x' * X * (y' * Y)) < 2 * A * ((x' + 1) * B * ((y' + 1) * C)) :=
      Nat.mul_lt_mul'' l2 m1
    have hn : 2 * (x' + 1) * (y' + 1) ≤ Z * X * Y := by
      have := Nat.mul_le_mul (Nat.mul_le_mul hZ2 hXx) hYy
      linarith
    have h5 := Nat.mul_le_mul_right (Z * X * Y) hxy16
    have h6 : 3 * (2 * A * ((x' + 1) * B * ((y' + 1) * C)))
        = 2 * (x' + 1) * (y' + 1) * (Z * X * Y + 2) := by rw [← hE]; ring
    have m3 : x' * y' * (Z * X * Y) < 2 * A * ((x' + 1) * B * ((y' + 1) * C)) := by
      have : Z * (x' * X * (y' * Y)) = x' * y' * (Z * X * Y) := by ring
      rw [← this]; exact m2
    generalize 2 * A * ((x' + 1) * B * ((y' + 1) * C)) = S at m3 h6
    generalize Z * X * Y = N at m3 h5 h6 hn
    linarith only [m3, h5, h6, hn]

/-! ## The number of cubes mod n: multiplicativity and closed forms at prime powers -/

section CubeCount

open Finset

/-- Number of distinct cubes mod n (A046530): #{x^3 mod n : 0 ≤ x < n}. -/
def cubeCount (n : ℕ) : ℕ := ((Finset.range n).image fun x => x ^ 3 % n).card

/-- The cubes of `ZMod n` as a finset. -/
def cubesZ (n : ℕ) [NeZero n] : Finset (ZMod n) := (univ : Finset (ZMod n)).image fun x => x ^ 3

lemma cubeCount_eq (n : ℕ) [NeZero n] : cubeCount n = (cubesZ n).card := by
  unfold cubeCount cubesZ
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod n))
      ((Finset.range n).image fun x => x ^ 3 % n : Finset ℕ) := by
    intro a ha b hb hab
    simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio] at ha hb
    obtain ⟨x, -, rfl⟩ := ha
    obtain ⟨y, -, rfl⟩ := hb
    have := (ZMod.natCast_eq_natCast_iff' _ _ n).mp hab
    simpa [Nat.mod_mod] using this
  rw [← card_image_of_injOn hinj, image_image]
  congr 1
  ext z
  simp only [mem_image, mem_range, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨x, -, rfl⟩
    exact ⟨x, by push_cast [ZMod.natCast_mod]; rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x.val, ZMod.val_lt x, ?_⟩
    rw [ZMod.natCast_mod]; push_cast; rw [ZMod.natCast_zmod_val]

lemma cubeCount_zero : cubeCount 0 = 0 := by simp [cubeCount]

lemma cubeCount_one : cubeCount 1 = 1 := by decide

/-- Multiplicativity (Chinese remainder theorem). -/
theorem cubeCount_mul {m k : ℕ} (h : Nat.Coprime m k) :
    cubeCount (m * k) = cubeCount m * cubeCount k := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [cubeCount_zero]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [cubeCount_zero]
  have : NeZero m := ⟨by omega⟩
  have : NeZero k := ⟨by omega⟩
  have : NeZero (m * k) := ⟨by positivity⟩
  rw [cubeCount_eq, cubeCount_eq, cubeCount_eq, ← card_product]
  let e := ZMod.chineseRemainder h
  rw [← card_image_of_injective _ e.injective]
  congr 1
  ext ⟨a, b⟩
  simp only [cubesZ, mem_image, mem_univ, true_and, mem_product]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, hx⟩
    rw [map_pow] at hx
    refine ⟨⟨(e x).1, ?_⟩, ⟨(e x).2, ?_⟩⟩
    · simpa using congrArg Prod.fst hx
    · simpa using congrArg Prod.snd hx
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨(e.symm (x, y)) ^ 3, ⟨_, rfl⟩, ?_⟩
    rw [map_pow, RingEquiv.apply_symm_apply, hx.symm, hy.symm]
    rfl

section PrimePow

variable {p : ℕ} (hp : p.Prime)
include hp

/-- In `ZMod (p^f)`, an element that is not a unit has `p ∣ val`. -/
lemma dvd_val_of_not_isUnit {f : ℕ} [NeZero (p ^ f)] (x : ZMod (p ^ f)) (hx : ¬ IsUnit x) :
    p ∣ x.val := by
  by_contra hd
  apply hx
  have hc : Nat.Coprime x.val (p ^ f) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd))
  refine ⟨ZMod.unitOfCoprime _ hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]

lemma not_isUnit_p {f : ℕ} (hf : 1 ≤ f) : ¬ IsUnit (p : ZMod (p ^ f)) := by
  intro hu
  have := (ZMod.isUnit_iff_coprime p (p ^ f)).mp hu
  have h2 := Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) this
  rw [Nat.coprime_self] at h2
  exact hp.one_lt.ne' h2

/-- The map `a ↦ p^3 a` from `ZMod (p^(f-3))` to `ZMod (p^f)`. -/
def shift3 (p f : ℕ) (a : ZMod (p ^ (f - 3))) : ZMod (p ^ f) := (p : ZMod (p ^ f)) ^ 3 * (a.val : ZMod (p ^ f))

omit hp in
lemma shift3_natCast (f a : ℕ) [NeZero (p ^ (f - 3))] :
    shift3 p f (a : ZMod (p ^ (f - 3))) = (p : ZMod (p ^ f)) ^ 3 * (a : ZMod (p ^ f)) := by
  unfold shift3
  rw [ZMod.val_natCast]
  have : ((p ^ 3 * (a % p ^ (f - 3)) : ℕ) : ZMod (p ^ f)) = ((p ^ 3 * a : ℕ) : ZMod (p ^ f)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    apply Nat.ModEq.of_dvd (show p ^ f ∣ p ^ 3 * p ^ (f - 3) by
      rw [← pow_add]; exact pow_dvd_pow p (by omega))
    exact Nat.ModEq.mul_left' _ (Nat.mod_modEq a _)
  push_cast at this
  exact this

lemma shift3_injective (f : ℕ) [NeZero (p ^ (f - 3))] : Function.Injective (shift3 p f) := by
  intro a b hab
  rcases Nat.lt_or_ge f 3 with hf | hf
  · have : p ^ (f - 3) = 1 := by rw [show f - 3 = 0 by omega, pow_zero]
    have hs : Subsingleton (ZMod (p ^ (f - 3))) := by rw [this]; infer_instance
    exact Subsingleton.elim a b
  unfold shift3 at hab
  have h3 : ((p ^ 3 * a.val : ℕ) : ZMod (p ^ f)) = ((p ^ 3 * b.val : ℕ) : ZMod (p ^ f)) := by
    push_cast; exact hab
  rw [ZMod.natCast_eq_natCast_iff] at h3
  have hpf : p ^ f = p ^ 3 * p ^ (f - 3) := by rw [← pow_add]; congr 1; omega
  rw [hpf] at h3
  have := Nat.ModEq.mul_left_cancel' (pow_ne_zero 3 hp.ne_zero) h3
  apply ZMod.val_injective
  exact Nat.ModEq.eq_of_lt_of_lt this (ZMod.val_lt a) (ZMod.val_lt b)

/-- The cubes of the unit group, pushed to `ZMod n`. -/
def unitCubes (n : ℕ) [NeZero n] : Finset (ZMod n) :=
  ((univ : Finset (ZMod n)ˣ).image fun u => u ^ 3).image Units.val

/-- Split of the cubes mod `p^f` into unit cubes and `p^3` times cubes mod `p^(f-3)`. -/
lemma cubesZ_split (f : ℕ) [NeZero (p ^ f)] [NeZero (p ^ (f - 3))] :
    cubesZ (p ^ f) = unitCubes (p ^ f) ∪ (cubesZ (p ^ (f - 3))).image (shift3 p f) := by
  ext y
  simp only [cubesZ, unitCubes, mem_union, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : IsUnit x
    · obtain ⟨u, rfl⟩ := hx
      left; exact ⟨u ^ 3, ⟨u, rfl⟩, by push_cast; rfl⟩
    · right
      obtain ⟨z, hz⟩ := dvd_val_of_not_isUnit hp x hx
      refine ⟨((z ^ 3 : ℕ) : ZMod (p ^ (f - 3))), ⟨(z : ZMod (p ^ (f - 3))), by push_cast; rfl⟩, ?_⟩
      rw [shift3_natCast, ← ZMod.natCast_zmod_val x, hz]
      push_cast; ring
  · rintro (⟨_, ⟨u, rfl⟩, rfl⟩ | ⟨_, ⟨z, rfl⟩, rfl⟩)
    · exact ⟨u, by push_cast; rfl⟩
    · refine ⟨(p : ZMod (p ^ f)) * (z.val : ZMod (p ^ f)), ?_⟩
      have : z ^ 3 = ((z.val ^ 3 : ℕ) : ZMod (p ^ (f - 3))) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [this, shift3_natCast]
      push_cast; ring

lemma unitCubes_disjoint (f : ℕ) (hf : 1 ≤ f) [NeZero (p ^ f)] [NeZero (p ^ (f - 3))] :
    Disjoint (unitCubes (p ^ f)) ((cubesZ (p ^ (f - 3))).image (shift3 p f)) := by
  rw [disjoint_left]
  intro y hy hy'
  simp only [unitCubes, mem_image, mem_univ, true_and] at hy hy'
  obtain ⟨_, ⟨u, rfl⟩, rfl⟩ := hy
  obtain ⟨a, -, ha⟩ := hy'
  have hu : IsUnit (shift3 p f a) := by rw [ha]; exact Units.isUnit _
  unfold shift3 at hu
  have := isUnit_of_mul_isUnit_left hu
  rw [isUnit_pow_iff (by norm_num)] at this
  exact not_isUnit_p hp hf this

/-- `c(p^f) = #(unit cubes mod p^f) + c(p^(f-3))` for `f ≥ 1`. -/
theorem cubeCount_prime_pow_step (f : ℕ) (hf : 1 ≤ f) [NeZero (p ^ f)] :
    cubeCount (p ^ f) =
      ((univ : Finset (ZMod (p ^ f))ˣ).image fun u => u ^ 3).card + cubeCount (p ^ (f - 3)) := by
  have : NeZero (p ^ (f - 3)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [cubeCount_eq, cubeCount_eq, cubesZ_split hp f,
    card_union_of_disjoint (unitCubes_disjoint hp f hf),
    card_image_of_injective _ (shift3_injective hp f), unitCubes,
    card_image_of_injective _ Units.val_injective]

end PrimePow

/-- In a finite commutative group, the number of cubes is `|G| / gcd(|G|, 3)` when `G` is cyclic. -/
lemma card_cubes_cyclic {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G] :
    ((univ : Finset G).image fun u => u ^ 3).card = Nat.card G / (Nat.card G).gcd 3 := by
  rw [← IsCyclic.card_powMonoidHom_range]
  rw [← SetLike.coe_sort_coe, MonoidHom.coe_range, Nat.card_eq_card_toFinset, Set.toFinset_range]
  rfl

lemma card_cubes_coprime {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (h : (Nat.card G).Coprime 3) :
    ((univ : Finset G).image fun u => u ^ 3).card = Nat.card G := by
  rw [Nat.card_eq_fintype_card, ← card_univ]
  congr 1
  rw [eq_univ_iff_forall]
  intro g
  simp only [mem_image, mem_univ, true_and]
  exact ⟨(powCoprime h).symm g, by
    have := (powCoprime h).apply_symm_apply g
    rwa [powCoprime_apply] at this⟩

/-- For a prime `q ≢ 1 (mod 3)`, `q ≠ 3`: `c(q^f) = (q-1) q^(f-1) + c(q^(f-3))` for `f ≥ 1`. -/
theorem cubeCount_step_two {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) (f : ℕ) :
    cubeCount (q ^ (f + 1)) = (q - 1) * q ^ f + cubeCount (q ^ (f + 1 - 3)) := by
  have : NeZero (q ^ (f + 1)) := ⟨pow_ne_zero _ hq.ne_zero⟩
  rw [cubeCount_prime_pow_step hq (f + 1) (by omega)]
  congr 1
  have hcard : Nat.card (ZMod (q ^ (f + 1)))ˣ = q ^ f * (q - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hq]
  rw [card_cubes_coprime, hcard]
  · ring
  rw [hcard]
  apply Nat.coprime_mul_iff_left.mpr ⟨?_, ?_⟩
  · apply Nat.Coprime.pow_left
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; omega
  · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    have := hq.two_le; omega

/-- For a prime `p ≡ 1 (mod 3)`: `3 c(p^f) = (p-1) p^(f-1) + 3 c(p^(f-3))` for `f ≥ 1`. -/
theorem cubeCount_step_one {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) (f : ℕ) :
    3 * cubeCount (p ^ (f + 1)) = (p - 1) * p ^ f + 3 * cubeCount (p ^ (f + 1 - 3)) := by
  have : NeZero (p ^ (f + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [cubeCount_prime_pow_step hp (f + 1) (by omega), mul_add]
  congr 1
  have := ZMod.isCyclic_units_of_prime_pow p hp (by omega) (f + 1)
  have hcard : Nat.card (ZMod (p ^ (f + 1)))ˣ = p ^ f * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]
  rw [card_cubes_cyclic, hcard]
  have h3 : 3 ∣ p - 1 := by omega
  have hg : (p ^ f * (p - 1)).gcd 3 = 3 := Nat.gcd_eq_right (dvd_mul_of_dvd_right h3 _)
  rw [hg]
  obtain ⟨k, hk⟩ := h3
  rw [hk, show p ^ f * (3 * k) = 3 * (p ^ f * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  ring

/-- Closed form at primes `q ≡ 2 (mod 3)`: `c(q^e) = cq q e` (hypothesis `h2` below). -/
theorem cubeCount_prime_pow_two {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) :
    ∀ e, cubeCount (q ^ e) = cq q e
  | 0 => by simp [cubeCount_one, cq, s1]
  | 1 => by
    have h := cubeCount_step_two hq hq3 0
    norm_num [cubeCount_one] at h
    simp [cq, s1]; omega
  | 2 => by
    have h := cubeCount_step_two hq hq3 1
    rw [h, show 1 + 1 - 3 = 0 by rfl, pow_zero, cubeCount_one]
    simp [cq, s1]; ring
  | e + 3 => by
    have h := cubeCount_step_two hq hq3 (e + 2)
    have ih := cubeCount_prime_pow_two hq hq3 e
    rw [show e + 2 + 1 - 3 = e by omega, ih] at h
    rw [h]
    show (q - 1) * q ^ (e + 2) + (1 + (q - 1) * s1 q e) = 1 + (q - 1) * (q ^ (e + 2) + s1 q e)
    ring

/-- Closed form at primes `p ≡ 1 (mod 3)`: `3 c(p^e) = 3 + (p - 1) s1 p e` (hypothesis `h1` below). -/
theorem cubeCount_prime_pow_one {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    ∀ e, 3 * cubeCount (p ^ e) = 3 + (p - 1) * s1 p e
  | 0 => by simp [cubeCount_one, s1]
  | 1 => by
    have h := cubeCount_step_one hp hp3 0
    norm_num [cubeCount_one] at h
    simp [s1]; omega
  | 2 => by
    have h := cubeCount_step_one hp hp3 1
    rw [h, show 1 + 1 - 3 = 0 by rfl, pow_zero, cubeCount_one]
    simp [s1]; ring
  | e + 3 => by
    have h := cubeCount_step_one hp hp3 (e + 2)
    have ih := cubeCount_prime_pow_one hp hp3 e
    rw [show e + 2 + 1 - 3 = e by omega, ih] at h
    rw [h]
    show (p - 1) * p ^ (e + 2) + (3 + (p - 1) * s1 p e) = 3 + (p - 1) * (p ^ (e + 2) + s1 p e)
    ring

/-- Rung R2 with the hypotheses discharged: no `n = 2^e x^a y^b` (`x ≠ y` odd primes,
`e, a, b ≥ 1`) satisfies `3 c(n) = n + 2`, where `c = cubeCount` is the number of cubes mod n. -/
theorem three_cubeCount_ne_two_and_two_odd {x y e a b : ℕ} (hx : x.Prime) (hy : y.Prime)
    (hx2 : x ≠ 2) (hy2 : y ≠ 2) (hxy : x ≠ y) (he : 1 ≤ e) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    3 * cubeCount (2 ^ e * x ^ a * y ^ b) ≠ 2 ^ e * x ^ a * y ^ b + 2 :=
  three_c_ne_two_and_two_odd cubeCount (fun _ _ h => cubeCount_mul h)
    (fun _ e hq hq3 => cubeCount_prime_pow_two hq hq3 e)
    (fun _ e hp hp3 => cubeCount_prime_pow_one hp hp3 e) hx hy hx2 hy2 hxy he ha hb

end CubeCount
