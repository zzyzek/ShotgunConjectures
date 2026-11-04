import Mathlib

/-
OEIS-A004050 (Mathlib). Conjecture (OEIS wiki Talk:Conjectures/List, A004050; see A085634):
only 5, 11, 17, 35 and 259 are 2^a + 3^b in two different ways. README result: true, given
Ellison's 1971 bound |2^x - 3^y| > 2^x e^(-x/10) for x ≥ 12, x ∉ {13, 14, 16, 19, 27}.

Main theorem `A004050_main`: assuming Ellison's bound (`EllisonBound`, stated over ℝ as quoted
in the README), a natural number v has two representations v = 2^a + 3^b = 2^c + 3^d with
(a, b) ≠ (c, d) iff v ∈ {5, 11, 17, 35, 259}.

`A004050_reduction` (unconditional): if 2^a + 3^b = 2^c + 3^d with c < a, then b < d ≤ a and
|2^a - 3^d| ≤ 4a. Proof: 2^c(2^f - 1) = 3^b(3^e - 1) (f = a - c, e = d - b), so 2^c ∣ 3^e - 1
and 3^b ∣ 2^f - 1; lifting the exponent (Mathlib `padicValNat.pow_two_sub_pow`,
`padicValNat.pow_sub_pow`) gives 2^c ≤ 4e and 3^b ≤ 3f; 3^d - 3^b < 2^a gives d ≤ a.
`small_of_ellison`: Ellison's bound and |2^a - 3^d| ≤ 4a force a ≤ 27 (since
(4a)^10·3^a ≤ 1024^a for a ≥ 12 and e < 3). The case a ≤ 27 is a kernel enumeration.

Outside Lean: Ellison's bound itself (F. Ellison, Sém. Théorie Nombres Bordeaux 1971, as quoted
in M. Waldschmidt, arXiv:0908.4031; a hypothesis of `A004050_main`).
-/

/-- Ellison (1971): |2^x - 3^y| > 2^x e^(-x/10) for x ≥ 12, x ∉ {13, 14, 16, 19, 27}. -/
def EllisonBound : Prop :=
  ∀ x y : ℕ, 12 ≤ x → x ≠ 13 → x ≠ 14 → x ≠ 16 → x ≠ 19 → x ≠ 27 →
    (2 : ℝ) ^ x * Real.exp (-(x : ℝ) / 10) < |(2 : ℝ) ^ x - (3 : ℝ) ^ y|

/-- v = 2^a + 3^b in two different ways. -/
def TwoWays (v : ℕ) : Prop :=
  ∃ a b c d : ℕ, (a, b) ≠ (c, d) ∧ v = 2 ^ a + 3 ^ b ∧ v = 2 ^ c + 3 ^ d

theorem pow3_mod4_odd (e : ℕ) (he : Odd e) : 3 ^ e % 4 = 3 := by
  obtain ⟨k, rfl⟩ := he
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

theorem pow2_mod3_odd (f : ℕ) (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

/-- 2^c ∣ 3^e - 1 (e ≥ 1) implies 2^c ≤ 4e. -/
theorem two_bound (c e : ℕ) (he : 1 ≤ e) (h : 2 ^ c ∣ 3 ^ e - 1) : 2 ^ c ≤ 4 * e := by
  have h3 : 1 < 3 ^ e := Nat.one_lt_pow (by omega) (by norm_num)
  rcases Nat.even_or_odd e with hev | hod
  · have := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num) (by norm_num)
      (show e ≠ 0 by omega) hev
    rw [one_pow] at this
    have h4 : padicValNat 2 (3 + 1) = 2 := by
      rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have h2 : padicValNat 2 (3 - 1) = 1 := by
      rw [show (3 - 1 : ℕ) = 2 by norm_num]; exact padicValNat_self
    rw [h4, h2] at this
    have hc : c ≤ padicValNat 2 (3 ^ e - 1) :=
      (padicValNat_dvd_iff_le (by omega)).mp h
    have hpe : 2 ^ padicValNat 2 e ≤ e := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    calc 2 ^ c ≤ 2 ^ (2 + padicValNat 2 e) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 * 2 ^ padicValNat 2 e := by rw [pow_add]; norm_num
      _ ≤ 4 * e := by omega
  · have h4 := pow3_mod4_odd e hod
    rcases Nat.lt_or_ge c 2 with hc | hc
    · interval_cases c <;> omega
    · exfalso
      have : 4 ∣ 3 ^ e - 1 := (Nat.pow_dvd_pow 2 hc).trans h
      omega

/-- 3^b ∣ 2^f - 1 (f ≥ 1) implies 3^b ≤ 3f. -/
theorem three_bound (b f : ℕ) (hf : 1 ≤ f) (h : 3 ^ b ∣ 2 ^ f - 1) : 3 ^ b ≤ 3 * f := by
  have h2 : 1 < 2 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; omega
  have h3 : 3 ∣ 2 ^ f - 1 := (dvd_pow_self 3 (by omega)).trans h
  rcases Nat.even_or_odd f with ⟨g, hg⟩ | hod
  · have hg0 : g ≠ 0 := by omega
    have e4 : 2 ^ f = 4 ^ g := by rw [hg, ← two_mul, pow_mul]; norm_num
    have := @padicValNat.pow_sub_pow 4 1 3 ⟨Nat.prime_three⟩ (by decide) (by norm_num)
      (by norm_num) (by norm_num) g hg0
    rw [one_pow, show (4 - 1 : ℕ) = 3 by norm_num, padicValNat_self] at this
    have : b ≤ padicValNat 3 (4 ^ g - 1) := by
      have : (3 : ℕ) ^ b ∣ 4 ^ g - 1 := by rw [← e4]; exact h
      exact (@padicValNat_dvd_iff_le 3 ⟨Nat.prime_three⟩ _ _ (by
        have : 1 < 4 ^ g := Nat.one_lt_pow hg0 (by norm_num)
        omega)).mp this
    have hpg : 3 ^ padicValNat 3 g ≤ g := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    calc 3 ^ b ≤ 3 ^ (1 + padicValNat 3 g) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 * 3 ^ padicValNat 3 g := by rw [pow_add]; norm_num
      _ ≤ 3 * f := by omega
  · have := pow2_mod3_odd f hod
    omega

theorem A004050_reduction (a b c d : ℕ) (h : 2 ^ a + 3 ^ b = 2 ^ c + 3 ^ d) (hca : c < a) :
    b < d ∧ d ≤ a ∧ |(2 : ℤ) ^ a - 3 ^ d| ≤ 4 * a := by
  have h2 : 2 ^ c < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) hca
  have hbd : b < d := by
    by_contra hc
    push Not at hc
    have : 3 ^ d ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hc
    omega
  set f := a - c
  set e := d - b
  have ha : 2 ^ a = 2 ^ c * 2 ^ f := by rw [← pow_add]; congr 1; omega
  have hd : 3 ^ d = 3 ^ b * 3 ^ e := by rw [← pow_add]; congr 1; omega
  have hf1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have he1 : 1 ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
  have key : 2 ^ c * (2 ^ f - 1) = 3 ^ b * (3 ^ e - 1) := by
    rw [Nat.mul_sub, Nat.mul_sub, mul_one, mul_one, ← ha, ← hd]; omega
  have hc2 : 2 ^ c ∣ 3 ^ e - 1 := by
    have : 2 ^ c ∣ 3 ^ b * (3 ^ e - 1) := ⟨_, key.symm⟩
    exact (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_left this
  have hb3 : 3 ^ b ∣ 2 ^ f - 1 := by
    have : 3 ^ b ∣ 2 ^ c * (2 ^ f - 1) := ⟨_, key⟩
    exact (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left this
  have hB2 := two_bound c e (by omega) hc2
  have hB3 := three_bound b f (by omega) hb3
  have hda : d ≤ a := by
    by_contra hc
    push Not at hc
    have h1 : 3 * 3 ^ b ≤ 3 ^ d := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hbd
    have h3 : 3 * 3 ^ a ≤ 3 ^ d := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hc
    have h4 : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
    omega
  refine ⟨hbd, hda, ?_⟩
  have hz : (2 : ℤ) ^ a - 3 ^ d = 2 ^ c - 3 ^ b := by
    have : ((2 ^ a + 3 ^ b : ℕ) : ℤ) = ((2 ^ c + 3 ^ d : ℕ) : ℤ) := by rw [h]
    push_cast at this; linarith
  rw [hz, abs_le]
  have hB2' : ((2 ^ c : ℕ) : ℤ) ≤ 4 * a := by exact_mod_cast (show 2 ^ c ≤ 4 * a by omega)
  have hB3' : ((3 ^ b : ℕ) : ℤ) ≤ 4 * a := by exact_mod_cast (show 3 ^ b ≤ 4 * a by omega)
  push_cast at hB2' hB3'
  constructor
  · have : (0 : ℤ) ≤ 2 ^ c := by positivity
    linarith
  · have : (0 : ℤ) ≤ 3 ^ b := by positivity
    linarith

theorem nat_ineq : ∀ a, 12 ≤ a → (4 * a) ^ 10 * 3 ^ a ≤ 1024 ^ a := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
    have h1 : (12 * (4 * (a + 1))) ^ 10 ≤ (13 * (4 * a)) ^ 10 :=
      Nat.pow_le_pow_left (by omega) 10
    rw [mul_pow 12 (4 * (a + 1)) 10, mul_pow 13 (4 * a) 10] at h1
    have h2 : 12 ^ 10 * ((4 * (a + 1)) ^ 10 * 3 ^ (a + 1)) ≤ 12 ^ 10 * 1024 ^ (a + 1) := by
      calc 12 ^ 10 * ((4 * (a + 1)) ^ 10 * 3 ^ (a + 1))
          = (12 ^ 10 * (4 * (a + 1)) ^ 10) * 3 ^ a * 3 := by ring
        _ ≤ (13 ^ 10 * (4 * a) ^ 10) * 3 ^ a * 3 := by
            apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; exact h1
        _ = 13 ^ 10 * 3 * ((4 * a) ^ 10 * 3 ^ a) := by ring
        _ ≤ 13 ^ 10 * 3 * 1024 ^ a := Nat.mul_le_mul_left _ ih
        _ ≤ 12 ^ 10 * 1024 * 1024 ^ a := by apply Nat.mul_le_mul_right; norm_num
        _ = 12 ^ 10 * 1024 ^ (a + 1) := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

theorem small_of_ellison (hE : EllisonBound) (a d : ℕ) (h : |(2 : ℤ) ^ a - 3 ^ d| ≤ 4 * a) :
    a ≤ 27 := by
  by_contra hc
  push Not at hc
  have hE' := hE a d (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hR : |(2 : ℝ) ^ a - (3 : ℝ) ^ d| ≤ 4 * a := by exact_mod_cast h
  have hlt : (2 : ℝ) ^ a < 4 * a * Real.exp ((a : ℝ) / 10) := by
    have hexp : Real.exp (-(a : ℝ) / 10) * Real.exp ((a : ℝ) / 10) = 1 := by
      rw [← Real.exp_add, show -(a : ℝ) / 10 + a / 10 = 0 by ring, Real.exp_zero]
    have hpos := Real.exp_pos ((a : ℝ) / 10)
    have := lt_of_lt_of_le hE' hR
    calc (2 : ℝ) ^ a = (2 : ℝ) ^ a * Real.exp (-(a : ℝ) / 10) * Real.exp ((a : ℝ) / 10) := by
          rw [mul_assoc, hexp, mul_one]
      _ < 4 * a * Real.exp ((a : ℝ) / 10) := mul_lt_mul_of_pos_right this hpos
  have h10 : ((2 : ℝ) ^ a) ^ 10 < (4 * a * Real.exp ((a : ℝ) / 10)) ^ 10 :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  have he : Real.exp ((a : ℝ) / 10) ^ 10 = Real.exp 1 ^ a := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have he3 : Real.exp 1 ^ a ≤ (3 : ℝ) ^ a :=
    pow_le_pow_left₀ (Real.exp_pos 1).le (by have := Real.exp_one_lt_d9; linarith) a
  rw [mul_pow, he] at h10
  have h1024 : ((2 : ℝ) ^ a) ^ 10 = (1024 : ℝ) ^ a := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h1024] at h10
  have hn := nat_ineq a (by omega)
  have hn' : ((4 * a) ^ 10 * 3 ^ a : ℝ) ≤ (1024 : ℝ) ^ a := by exact_mod_cast hn
  have : ((4 : ℝ) * a) ^ 10 * Real.exp 1 ^ a ≤ ((4 : ℝ) * a) ^ 10 * 3 ^ a :=
    mul_le_mul_of_nonneg_left he3 (by positivity)
  linarith

theorem enum : (List.range 28).all (fun a => (List.range (a + 1)).all (fun d =>
    (List.range d).all (fun b => (List.range a).all (fun c =>
      !(2 ^ a + 3 ^ b == 2 ^ c + 3 ^ d) || [5, 11, 17, 35, 259].contains (2 ^ a + 3 ^ b))))) = true := by
  decide +kernel

theorem ordered (hE : EllisonBound) (a b c d : ℕ) (h : 2 ^ a + 3 ^ b = 2 ^ c + 3 ^ d) (hca : c < a) :
    2 ^ a + 3 ^ b ∈ ({5, 11, 17, 35, 259} : Finset ℕ) := by
  obtain ⟨hbd, hda, habs⟩ := A004050_reduction a b c d h hca
  have ha := small_of_ellison hE a d habs
  have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp enum
    a (List.mem_range.mpr (by omega))) d (List.mem_range.mpr (by omega))) b
    (List.mem_range.mpr hbd)) c (List.mem_range.mpr hca)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at this
  rcases this with h' | h'
  · exact absurd h h'
  · simpa using h'

theorem A004050_main (hE : EllisonBound) (v : ℕ) :
    TwoWays v ↔ v ∈ ({5, 11, 17, 35, 259} : Finset ℕ) := by
  constructor
  · rintro ⟨a, b, c, d, hne, h1, h2⟩
    rcases lt_trichotomy c a with hca | hca | hca
    · rw [h1]; exact ordered hE a b c d (h1 ▸ h2) hca
    · subst hca
      have : 3 ^ b = 3 ^ d := by omega
      have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
      exact absurd (by rw [this]) hne
    · rw [h2]; exact ordered hE c d a b (h2 ▸ h1) hca
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 0, 1, 1, by decide, by norm_num, by norm_num⟩
    · exact ⟨3, 1, 1, 2, by decide, by norm_num, by norm_num⟩
    · exact ⟨4, 0, 3, 2, by decide, by norm_num, by norm_num⟩
    · exact ⟨5, 1, 3, 3, by decide, by norm_num, by norm_num⟩
    · exact ⟨8, 1, 4, 5, by decide, by norm_num, by norm_num⟩
