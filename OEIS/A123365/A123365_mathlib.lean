import Mathlib

/-
Core question core-multiplicative-exact-target (OEIS-A123365), two-prime-factor case.

c(n) = number of cubes mod n, defined as `cubeCount n = #{x^3 mod n : 0 <= x < n}` (A046530).
Proved here for `cubeCount` (section CubeCount at the end):
* `cubeCount_mul`: c is multiplicative on coprime arguments (CRT);
* `cubeCount_prime_pow_two`: q prime, q % 3 = 2: c(q^e) = 1 + (q - 1) s1(q, e) (`cq`);
* `cubeCount_prime_pow_one`: p prime, p % 3 = 1: 3 c(p^e) = 3 + (p - 1) s1(p, e);
where s1(q, e) = sum of q^(j-1) over 1 <= j <= e with j = e (mod 3).

Checked here (Lean + Mathlib):
* `cq_equation_no_solution`: for primes p, q with p % 3 = 1, q % 3 = 2 and e >= 1,
  (p + 2) c(q^e) != p q^e + 2 (with c(q^e) given by the closed form `cq`).
* `three_c_eq_one_factor`, `three_c_ne_of_two_factors`: the statements below for any c with the
  three properties above (stated as hypotheses).
* `three_cubeCount_eq_one_factor`: 3 c(x^a) = x^a + 2 with x prime, a >= 1 forces a = 1, x = 1 (mod 3).
* `three_cubeCount_prime`: 3 c(p) = p + 2 for every prime p = 1 (mod 3).
* `three_cubeCount_ne_of_two_factors`: for distinct primes x, y and a, b >= 1,
  3 c(x^a y^b) != x^a y^b + 2; that is, no n with exactly two distinct prime factors
  satisfies 3c(n) = n + 2.
NOT checked here: nothing beyond reading the definition of `cubeCount` as A046530.
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

/-- Two prime factors, hypotheses discharged: no `n = x^a y^b` (`x ≠ y` primes, `a, b ≥ 1`)
satisfies `3 c(n) = n + 2`, where `c = cubeCount` is the number of cubes mod n. -/
theorem three_cubeCount_ne_of_two_factors {x y a b : ℕ} (hx : x.Prime) (hy : y.Prime)
    (hxy : x ≠ y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    3 * cubeCount (x ^ a * y ^ b) ≠ x ^ a * y ^ b + 2 :=
  three_c_ne_of_two_factors cubeCount (fun _ _ h => cubeCount_mul h)
    (fun _ e hq hq3 => cubeCount_prime_pow_two hq hq3 e)
    (fun _ e hp hp3 => cubeCount_prime_pow_one hp hp3 e) hx hy hxy ha hb

/-- One prime factor, hypotheses discharged: `3 c(x^a) = x^a + 2` with `x` prime and `a ≥ 1`
forces `a = 1` and `x ≡ 1 (mod 3)`. -/
theorem three_cubeCount_eq_one_factor {x a : ℕ} (hx : x.Prime) (ha : 1 ≤ a)
    (hE : 3 * cubeCount (x ^ a) = x ^ a + 2) : a = 1 ∧ x % 3 = 1 :=
  three_c_eq_one_factor cubeCount (fun _ e hq hq3 => cubeCount_prime_pow_two hq hq3 e)
    (fun _ e hp hp3 => cubeCount_prime_pow_one hp hp3 e) hx ha hE

/-- Converse direction for primes: `3 c(p) = p + 2` for every prime `p ≡ 1 (mod 3)`. -/
theorem three_cubeCount_prime {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    3 * cubeCount p = p + 2 := by
  have h := cubeCount_prime_pow_one hp hp3 1
  rw [pow_one] at h
  rw [h]; simp [s1]; omega

end CubeCount
