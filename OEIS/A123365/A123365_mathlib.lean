import Mathlib

/-
Core question core-multiplicative-exact-target (OEIS-A123365), two-prime-factor case.

c(n) = number of cubes mod n. Closed forms used as hypotheses (NOT proved here; checked by
brute force in work/tier2/A123365/probe.py and scripts/cube_checks.py beside this file):
* c is multiplicative on coprime arguments (CRT);
* q prime, q % 3 = 2: c(q^e) = 1 + (q - 1) s1(q, e) (`cq`);
* p prime, p % 3 = 1: 3 c(p^e) = 3 + (p - 1) s1(p, e);
where s1(q, e) = sum of q^(j-1) over 1 ≤ j ≤ e with j ≡ e (mod 3).

Checked here (Lean + Mathlib, no hypotheses on c):
* `cq_equation_no_solution`: for primes p, q with p % 3 = 1, q % 3 = 2 and e ≥ 1,
  (p + 2) c(q^e) ≠ p q^e + 2 (with c(q^e) given by the closed form `cq`).
Checked here, conditional on the three closed-form hypotheses above:
* `three_c_eq_one_factor`: 3 c(x^a) = x^a + 2 with x prime, a ≥ 1 forces a = 1, x ≡ 1 (mod 3).
* `three_c_ne_of_two_factors`: for distinct primes x, y and a, b ≥ 1,
  3 c(x^a y^b) ≠ x^a y^b + 2; that is, no n with exactly two distinct prime factors
  satisfies 3c(n) = n + 2.
-/

open Finset

/-- s1 q e = sum of q^(j-1) over 1 ≤ j ≤ e, j ≡ e (mod 3). -/
def s1 (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => q
  | (e + 3) => q ^ (e + 2) + s1 q e

/-- G q e = 1 + q + ... + q^(e-1). -/
def G (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | (e + 1) => G q e + q ^ e

/-- Closed form of the number of cubes mod q^e for a prime q ≡ 2 (mod 3). -/
def cq (q e : ℕ) : ℕ := 1 + (q - 1) * s1 q e

lemma pow_eq_G (q : ℕ) (hq : 1 ≤ q) : ∀ e, q ^ e = 1 + (q - 1) * G q e
  | 0 => by simp [G]
  | e + 1 => by
    have ih := pow_eq_G q hq e
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [G, Nat.add_sub_cancel] at ih ⊢
    rw [pow_succ, ih]; ring

lemma G_mod (q : ℕ) (hq : 2 ≤ q) : ∀ e, G q (e + 1) % q = 1
  | 0 => by simp [G]; exact Nat.mod_eq_of_lt hq
  | e + 1 => by
    have ih := G_mod q hq e
    have hd : q ∣ q ^ (e + 1) := dvd_pow_self q (by omega)
    show (G q (e + 1) + q ^ (e + 1)) % q = 1
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, ih]
    simp [Nat.mod_eq_of_lt hq]

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

/-- (p + 2) c(q^e) = p q^e + 2 has no solution with p, q prime, p ≡ 1, q ≡ 2 (mod 3),
e ≥ 1, where c(q^e) = `cq q e`. -/
theorem cq_equation_no_solution {p q e : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : p % 3 = 1)
    (hq3 : q % 3 = 2) (he : 1 ≤ e) : (p + 2) * cq q e ≠ p * q ^ e + 2 := by
  intro hEq
  have hq2 := hq.two_le
  have hp2 := hp.two_le
  -- Reduce to (p + 2) s1 = p G.
  have hpow := pow_eq_G q (by omega) e
  have hred : (p + 2) * s1 q e = p * G q e := by
    unfold cq at hEq
    rw [hpow] at hEq
    have h1 : (q - 1) * ((p + 2) * s1 q e) = (q - 1) * (p * G q e) := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hGq := G_mod q hq2 e'
  have hdecomp : e' + 1 = 3 * ((e' + 1) / 3) + (e' + 1) % 3 := (Nat.div_add_mod _ 3).symm
  have hsm := s1_mod q ((e' + 1) / 3) ((e' + 1) % 3)
  rw [← hdecomp] at hsm
  have hr : (e' + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  -- Case q ∣ s1: then q ∣ p G, so q = p, impossible mod 3.
  have caseDvd : q ∣ s1 q (e' + 1) → False := by
    intro hd
    have h1 : q ∣ p * G q (e' + 1) := hred ▸ dvd_mul_of_dvd_right hd _
    rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
    · rcases hp.eq_one_or_self_of_dvd q h2 with h3 | h3
      · omega
      · omega
    · have := Nat.mod_eq_zero_of_dvd h2; omega
  interval_cases hrr : (e' + 1) % 3
  · exact caseDvd (Nat.dvd_of_mod_eq_zero (by rw [hsm]; simp [s1]))
  · -- s1 ≡ 1 (mod q): then q ∣ 2, so q = 2.
    have hs1 : s1 q (e' + 1) % q = 1 := by rw [hsm]; simp [s1, Nat.mod_eq_of_lt hq2]
    have hmod : (p + 2) % q = p % q := by
      have : (p + 2) * s1 q (e' + 1) % q = p * G q (e' + 1) % q := by rw [hred]
      rw [Nat.mul_mod, hs1, Nat.mul_mod p, hGq] at this
      simpa using this
    have hq2' : q ∣ 2 := by
      have := (Nat.modEq_iff_dvd' (by omega : p ≤ p + 2)).mp hmod.symm
      simpa using this
    have hqeq : q = 2 := le_antisymm (Nat.le_of_dvd (by norm_num) hq2') hq2
    subst hqeq
    -- q = 2, e = 3t + 1.
    set t := (e' + 1) / 3 with ht
    have het : e' + 1 = 3 * t + 1 := by omega
    rw [het] at hred
    have hs := s1_two_mul t
    have hG : 2 ^ (3 * t + 1) = 1 + G 2 (3 * t + 1) := by
      have := pow_eq_G 2 (by norm_num) (3 * t + 1)
      simpa using this
    have h8 : (2 : ℕ) ^ (3 * t + 1) = 2 * 8 ^ t := by
      rw [pow_succ, pow_mul]; norm_num; ring
    rw [h8] at hG
    set u := 8 ^ t with hu
    have hp4 : 4 ≤ p := by omega
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · -- e = 1: (p + 2) * 1 = p * 1.
      rw [h0] at hred
      simp [s1, G] at hred
    · have hu8 : 8 ≤ u := by
        rw [hu]; calc 8 = 8 ^ 1 := by norm_num
          _ ≤ 8 ^ t := Nat.pow_le_pow_right (by norm_num) h0
      have hs' : 7 * s1 2 (3 * t + 1) + 1 = 8 * u := by rw [hs, pow_succ, hu]; ring
      -- (u - 1)(3p - 8) = 7 over ℤ.
      have hz : ((u : ℤ) - 1) * (3 * (p : ℤ) - 8) = 7 := by
        have a1 : ((p : ℤ) + 2) * (s1 2 (3 * t + 1) : ℤ) = (p : ℤ) * (G 2 (3 * t + 1) : ℤ) := by
          exact_mod_cast hred
        have a2 : 7 * (s1 2 (3 * t + 1) : ℤ) + 1 = 8 * (u : ℤ) := by exact_mod_cast hs'
        have a3 : 2 * (u : ℤ) = 1 + (G 2 (3 * t + 1) : ℤ) := by exact_mod_cast hG
        nlinarith
      have hu' : (8 : ℤ) ≤ u := by exact_mod_cast hu8
      have hp' : (4 : ℤ) ≤ p := by exact_mod_cast hp4
      nlinarith
  · exact caseDvd (Nat.dvd_of_mod_eq_zero (by rw [hsm]; simp [s1]))

/-! Bounds on s1 and G used for the two-prime-factor theorem. -/

lemma G_add_three (q e : ℕ) : G q (e + 3) = G q e + q ^ e + q ^ (e + 1) + q ^ (e + 2) := by
  simp only [G]

lemma s1_le_G (q : ℕ) (hq : 1 ≤ q) : ∀ e, s1 q e ≤ G q e ∧ (2 ≤ e → s1 q e + 1 ≤ G q e)
  | 0 => by simp [s1, G]
  | 1 => by simp [s1, G]
  | 2 => by simp [s1, G]
  | e + 3 => by
    have ih := (s1_le_G q hq e).1
    rw [G_add_three]
    show q ^ (e + 2) + s1 q e ≤ _ ∧ (_ → q ^ (e + 2) + s1 q e + 1 ≤ _)
    have h : 1 ≤ q ^ e := Nat.one_le_pow _ _ hq
    constructor <;> intros <;> omega

lemma pow_le_s1 (q : ℕ) : ∀ e, q ^ e ≤ s1 q (e + 1)
  | 0 => by simp [s1]
  | 1 => by simp [s1]
  | e + 2 => by show q ^ (e + 2) ≤ q ^ (e + 2) + s1 q e; omega

/-- For a prime q ≡ 2 (mod 3): q · cq(q, e) > (q - 1) q^e and cq(q, e) ≤ q^e. -/
lemma cq_bounds {q e : ℕ} (hq : 2 ≤ q) (he : 1 ≤ e) :
    (q - 1) * q ^ e < q * cq q e ∧ cq q e ≤ q ^ e := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have h1 := pow_le_s1 q e'
  have h2 := (s1_le_G q (by omega) (e' + 1)).1
  have hp := pow_eq_G q (by omega) (e' + 1)
  unfold cq
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have h3 := Nat.mul_le_mul_left (r * (r + 1)) h1
  constructor
  · rw [pow_succ]; nlinarith
  · rw [hp]; nlinarith

/-- Arithmetic core of the case where both primes are ≡ 2 (mod 3). -/
lemma both_two_aux {x y P Q C D : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (h1 : (x - 1) * P < x * C) (h2 : (y - 1) * Q < y * D) (h3 : x * y ≤ P * Q)
    (h4 : 2 * x * y + 1 ≥ 3 * x + 3 * y) (hE : 3 * (C * D) = P * Q + 2) : False := by
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2
  have F1 : (x' * P + 1) * (y' * Q + 1) ≤ ((x' + 1) * C) * ((y' + 1) * D) :=
    Nat.mul_le_mul h1 h2
  have h4' : (x' + 1) * (y' + 1) + 2 ≤ 3 * (x' * y') := by nlinarith
  have F2 := Nat.mul_le_mul_right (P * Q) h4'
  have F4 : (x' + 1) * (y' + 1) * (3 * (C * D)) = (x' + 1) * (y' + 1) * (P * Q + 2) := by
    rw [hE]
  nlinarith

/-- No n = x^a y^b (x ≠ y primes, a, b ≥ 1) satisfies 3 c(n) = n + 2, assuming c is
multiplicative and the closed forms of c at prime powers ≢ 0 (mod 3). -/
theorem three_c_ne_of_two_factors (c : ℕ → ℕ)
    (hmul : ∀ m k, Nat.Coprime m k → c (m * k) = c m * c k)
    (h2 : ∀ q e, q.Prime → q % 3 = 2 → c (q ^ e) = cq q e)
    (h1 : ∀ p e, p.Prime → p % 3 = 1 → 3 * c (p ^ e) = 3 + (p - 1) * s1 p e)
    {x y a b : ℕ} (hx : x.Prime) (hy : y.Prime) (hxy : x ≠ y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    3 * c (x ^ a * y ^ b) ≠ x ^ a * y ^ b + 2 := by
  intro hEq
  have hcop : Nat.Coprime (x ^ a) (y ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes hx hy).mpr hxy)
  rw [hmul _ _ hcop] at hEq
  have hx2 := hx.two_le
  have hy2 := hy.two_le
  -- 3 does not divide n.
  have h3n : ((x ^ a) * (y ^ b)) % 3 = 1 := by omega
  have hres : ∀ z k, z.Prime → 1 ≤ k → (z ^ k) ∣ (x ^ a) * (y ^ b) → z % 3 = 1 ∨ z % 3 = 2 := by
    intro z k hz hk hd
    rcases Nat.lt_or_ge (z % 3) 1 with h | h
    · exfalso
      have h3 : 3 ∣ z := by omega
      have : 3 ∣ (x ^ a) * (y ^ b) := h3.trans ((dvd_pow_self z (by omega)).trans hd)
      omega
    · omega
  have rx := hres x a hx ha (dvd_mul_right (x ^ a) (y ^ b))
  have ry := hres y b hy hb (dvd_mul_left (y ^ b) (x ^ a))
  -- Facts for the residue-1 prime powers.
  have one_bounds : ∀ p e, p.Prime → p % 3 = 1 → 1 ≤ e →
      (e = 1 → 3 * c (p ^ e) = p + 2) ∧ (2 ≤ e → 3 * c (p ^ e) + 2 ≤ p ^ e) ∧
      3 * c (p ^ e) ≤ p ^ e + 2 := by
    intro p e hp hp3 he
    have hp4 : 7 ≤ p := by
      have := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    have hc := h1 p e hp hp3
    have hpow := pow_eq_G p (by omega) e
    have hs := s1_le_G p (by omega) e
    refine ⟨fun h => ?_, fun h => ?_, ?_⟩
    · subst h; rw [hc]; simp [s1]; omega
    · have := hs.2 h
      have h4 : (p - 1) * (s1 p e + 1) ≤ (p - 1) * G p e := Nat.mul_le_mul_left _ this
      have h5 : (p - 1) * (s1 p e + 1) = (p - 1) * s1 p e + (p - 1) := by ring
      rw [hc, hpow]; omega
    · have h4 : (p - 1) * s1 p e ≤ (p - 1) * G p e := Nat.mul_le_mul_left _ hs.1
      rw [hc, hpow]; omega
  rcases rx with rx | rx <;> rcases ry with ry | ry
  · -- both ≡ 1: 9 c c' ≤ ((x ^ a)+2)((y ^ b)+2) < 3 (XY + 2).
    have bx := (one_bounds x a hx rx ha).2.2
    have bxy := (one_bounds y b hy ry hb).2.2
    have hX7 : 4 ≤ (x ^ a) := by
      have : 4 ≤ x := by omega
      calc 4 ≤ x := this
        _ = x ^ 1 := (pow_one x).symm
        _ ≤ (x ^ a) := Nat.pow_le_pow_right (by omega) ha
    have hY7 : 4 ≤ (y ^ b) := by
      have : 4 ≤ y := by omega
      calc 4 ≤ y := this
        _ = y ^ 1 := (pow_one y).symm
        _ ≤ (y ^ b) := Nat.pow_le_pow_right (by omega) hb
    have := Nat.mul_le_mul bx bxy
    nlinarith
  · -- x ≡ 1, y ≡ 2.
    have hcy := h2 y b hy ry
    have cb := cq_bounds hy2 hb
    rw [hcy] at hEq
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have ha1 : a = 1 := by omega
      have e1 := (one_bounds x a hx rx ha).1 ha1
      have key := cq_equation_no_solution hx hy rx ry hb
      subst ha1
      apply key
      calc (x + 2) * cq y b = 3 * c (x ^ 1) * cq y b := by rw [e1]
        _ = 3 * (c (x ^ 1) * cq y b) := by ring
        _ = x ^ 1 * y ^ b + 2 := hEq
        _ = x * y ^ b + 2 := by rw [pow_one]
    · have e2 := (one_bounds x a hx rx ha).2.1 ha2
      have := Nat.mul_le_mul_right (cq y b) e2
      nlinarith [cb.2]
  · -- x ≡ 2, y ≡ 1 (symmetric).
    have hcx := h2 x a hx rx
    have cb := cq_bounds hx2 ha
    rw [hcx] at hEq
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · have hb1 : b = 1 := by omega
      have e1 := (one_bounds y b hy ry hb).1 hb1
      have key := cq_equation_no_solution hy hx ry rx ha
      subst hb1
      apply key
      calc (y + 2) * cq x a = cq x a * (3 * c (y ^ 1)) := by rw [e1]; ring
        _ = 3 * (cq x a * c (y ^ 1)) := by ring
        _ = x ^ a * y ^ 1 + 2 := hEq
        _ = y * x ^ a + 2 := by rw [pow_one]; ring
    · have e2 := (one_bounds y b hy ry hb).2.1 hb2
      have := Nat.mul_le_mul_left (cq x a) e2
      nlinarith [cb.2]
  · -- both ≡ 2: 3 c c' > XY + 2.
    rw [h2 x a hx rx, h2 y b hy ry] at hEq
    have cx := cq_bounds hx2 ha
    have cy := cq_bounds hy2 hb
    -- wlog-free: use x y ≥ 2, one of them ≥ 5.
    have hxX : x ≤ (x ^ a) := by
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ (x ^ a) := Nat.pow_le_pow_right (by omega) ha
    have hyY : y ≤ (y ^ b) := by
      calc y = y ^ 1 := (pow_one y).symm
        _ ≤ (y ^ b) := Nat.pow_le_pow_right (by omega) hb
    have hxy5 : 2 * x * y + 1 ≥ 3 * x + 3 * y := by
      have hx5 : x = 2 ∨ 5 ≤ x := by omega
      have hy5 : y = 2 ∨ 5 ≤ y := by omega
      rcases hx5 with h | h <;> rcases hy5 with h' | h'
      · omega
      · subst h; omega
      · subst h'; omega
      · nlinarith
    exact both_two_aux hx2 hy2 cx.1 cy.1 (Nat.mul_le_mul hxX hyY) hxy5 hEq

/-- One prime factor: 3 c(x^a) = x^a + 2 forces a = 1 and x ≡ 1 (mod 3) (under the same
closed-form hypotheses; conversely 3 c(p) = p + 2 for such p by the closed form). -/
theorem three_c_eq_one_factor (c : ℕ → ℕ)
    (h2 : ∀ q e, q.Prime → q % 3 = 2 → c (q ^ e) = cq q e)
    (h1 : ∀ p e, p.Prime → p % 3 = 1 → 3 * c (p ^ e) = 3 + (p - 1) * s1 p e)
    {x a : ℕ} (hx : x.Prime) (ha : 1 ≤ a) (hE : 3 * c (x ^ a) = x ^ a + 2) :
    a = 1 ∧ x % 3 = 1 := by
  have hx2 := hx.two_le
  have hxX : x ≤ x ^ a := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ a := Nat.pow_le_pow_right (by omega) ha
  rcases Nat.lt_or_ge (x % 3) 1 with h0 | h0
  · exfalso
    have h3 : 3 ∣ x ^ a := (show 3 ∣ x by omega).trans (dvd_pow_self x (by omega))
    omega
  rcases Nat.lt_or_ge (x % 3) 2 with h1' | h2'
  · have hx3 : x % 3 = 1 := by omega
    refine ⟨?_, hx3⟩
    by_contra hne
    have ha2 : 2 ≤ a := by omega
    have hx7 : 7 ≤ x := by
      have h4 : x ≠ 4 := by rintro rfl; norm_num at hx
      omega
    have hc := h1 x a hx hx3
    have hpow := pow_eq_G x (by omega) a
    have hs := (s1_le_G x (by omega) a).2 ha2
    have h4 : (x - 1) * (s1 x a + 1) ≤ (x - 1) * G x a := Nat.mul_le_mul_left _ hs
    have h5 : (x - 1) * (s1 x a + 1) = (x - 1) * s1 x a + (x - 1) := by ring
    omega
  · exfalso
    have hx3 : x % 3 = 2 := by omega
    rw [h2 x a hx hx3] at hE
    have cb := cq_bounds hx2 ha
    rcases Nat.lt_or_ge x 5 with hx5 | hx5
    · have hx2' : x = 2 := by omega
      subst hx2'
      rcases Nat.lt_or_ge a 2 with ha2 | ha2
      · have : a = 1 := by omega
        subst this
        simp [cq, s1] at hE
      · have h4 : 4 ≤ 2 ^ a := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
        nlinarith [cb.1]
    · have k1 := cb.1
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at k1
      have k2 : 3 * (x' * (x' + 1) ^ a) < (x' + 1) * (3 * cq (x' + 1) a) := by
        have := Nat.mul_lt_mul_of_pos_left k1 (by norm_num : 0 < 3)
        linarith
      rw [hE] at k2
      have k3 := Nat.mul_le_mul_right ((x' + 1) ^ a) (show 4 ≤ x' by omega)
      nlinarith
