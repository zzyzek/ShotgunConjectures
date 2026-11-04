/-
OEIS A081320 (largest 3-smooth divisor of F(n)), conjecture: for n > 12 and
n ≢ 0 (mod 12), a(n) = a(n-12); and a(12k) = A065331(k)·144.

`smooth3 m = 2^(v_2 m) · 3^(v_3 m)` (v_p = `Nat.factorization`) is the largest
divisor of m of the form 2^i 3^j (`smooth3_spec`), so A081320(n) = smooth3 (fib n) and
A065331(k) = smooth3 k.

Main theorem `A081320_conjecture`: (i) for every n > 12 with ¬ 12 ∣ n,
smooth3 (fib n) = smooth3 (fib (n-12)); (ii) for every k ≥ 1,
smooth3 (fib (12k)) = 144 · smooth3 k.  This is the README result.

Proof.  fib(n+12) = 89·fib n + 144·fib(n+1), so 16 ∣ fib n ↔ 12 ∣ n and
9 ∣ fib n ↔ 12 ∣ n, and for 12 ∤ n the 2- and 3-adic valuations (≤ 3 and ≤ 1)
are unchanged by n ↦ n + 12.  For (ii): fib(2m) = F_m (F_m + 2F_(m-1)) and
fib(3m) = F_m (3F_(m-1)^2 + 3F_m F_(m-1) + 2F_m^2) give
v_2(F_(2m)) = v_2(F_m) + 1 when 4 ∣ F_m and v_3(F_(3m)) = v_3(F_m) + 1 when
3 ∣ F_m; strong divisibility gcd(F_a, F_b) = F_gcd(a,b) (Mathlib
`Nat.fib_gcd`) shows that multiplying the index by a number prime to p does
not change v_p.  Hence v_2(F_(12k)) = v_2(k) + 4, v_3(F_(12k)) = v_3(k) + 2.

Not checked: nothing outside Lean.
-/
import Mathlib

open Nat

/-- The largest divisor of m of the form 2^i·3^j. -/
def smooth3 (m : ℕ) : ℕ := 2 ^ m.factorization 2 * 3 ^ m.factorization 3

/-- smooth3 m is a divisor of m of the form 2^i·3^j, and every such divisor
divides it (so it is the largest one). -/
theorem smooth3_spec {m : ℕ} (hm : m ≠ 0) :
    smooth3 m ∣ m ∧ ∀ i j : ℕ, 2 ^ i * 3 ^ j ∣ m → 2 ^ i * 3 ^ j ∣ smooth3 m := by
  refine ⟨?_, ?_⟩
  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow _ _ (by norm_num)) (Nat.ordProj_dvd m 2) (Nat.ordProj_dvd m 3)
  · intro i j h
    have hi : i ≤ m.factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hm).1 (dvd_trans (Dvd.intro _ rfl) h)
    have hj : j ≤ m.factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hm).1 (dvd_trans (Dvd.intro_left _ rfl) h)
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hi) (Nat.pow_dvd_pow 3 hj)

lemma fact_eq {p m e : ℕ} (hp : p.Prime) (hm : m ≠ 0) (h1 : p ^ e ∣ m)
    (h2 : ¬ p ^ (e + 1) ∣ m) : m.factorization p = e := by
  have := (hp.pow_dvd_iff_le_factorization hm).1 h1
  by_contra hne
  exact h2 ((hp.pow_dvd_iff_le_factorization hm).2 (by omega))

lemma fibdvd {m n : ℕ} (h : m ∣ n) : fib m ∣ fib n := by
  have := Nat.fib_gcd m n
  rw [Nat.gcd_eq_left h] at this
  rw [this]; exact Nat.gcd_dvd_right _ _

lemma fib_add_twelve (n : ℕ) : fib (n + 12) = 89 * fib n + 144 * fib (n + 1) := by
  have := Nat.fib_add 11 n
  rw [show 11 + n + 1 = n + 12 by ring] at this
  rw [this]; norm_num [Nat.fib_add_two]

/-- 16 ∣ F_n ↔ 12 ∣ n, and 9 ∣ F_n ↔ 12 ∣ n. -/
lemma dvd_fib_iff (n : ℕ) : (16 ∣ fib n ↔ 12 ∣ n) ∧ (9 ∣ fib n ↔ 12 ∣ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 12 with h | h
    · interval_cases n <;> decide
    · obtain ⟨r, rfl⟩ : ∃ r, n = r + 12 := ⟨n - 12, by omega⟩
      have ih' := ih r (by omega)
      rw [fib_add_twelve]
      have e12 : 12 ∣ r + 12 ↔ 12 ∣ r := by omega
      rw [e12]
      constructor
      · rw [← ih'.1]
        constructor
        · intro hd
          have : 16 ∣ 89 * fib r := (Nat.dvd_add_left (Dvd.dvd.mul_right (by norm_num) _)).1 hd
          exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
        · intro hd
          exact Nat.dvd_add (Dvd.dvd.mul_left hd _) (Dvd.dvd.mul_right (by norm_num) _)
      · rw [← ih'.2]
        constructor
        · intro hd
          have : 9 ∣ 89 * fib r := (Nat.dvd_add_left (Dvd.dvd.mul_right (by norm_num) _)).1 hd
          exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
        · intro hd
          exact Nat.dvd_add (Dvd.dvd.mul_left hd _) (Dvd.dvd.mul_right (by norm_num) _)

/-- X = u·F + c·G with p^B ∣ c, p ∤ u, p^B ∤ F: v_p(X) = v_p(F). -/
lemma fact_shift {p B u c F G : ℕ} (hp : p.Prime) (hc : p ^ B ∣ c) (hu : Nat.Coprime p u)
    (hu0 : 0 < u) (hF : F ≠ 0) (hB : ¬ p ^ B ∣ F) :
    (u * F + c * G).factorization p = F.factorization p := by
  set e := F.factorization p
  have heB : e < B := by
    by_contra h; exact hB ((hp.pow_dvd_iff_le_factorization hF).2 (by omega))
  have hX : u * F + c * G ≠ 0 := by
    have : 0 < u * F := Nat.mul_pos hu0 (Nat.pos_of_ne_zero hF); omega
  apply fact_eq hp hX
  · exact Nat.dvd_add (Dvd.dvd.mul_left (Nat.ordProj_dvd F p) _)
      (Dvd.dvd.mul_right (dvd_trans (Nat.pow_dvd_pow p heB.le) hc) _)
  · intro hd
    have h1 : p ^ (e + 1) ∣ c * G := Dvd.dvd.mul_right (dvd_trans (Nat.pow_dvd_pow p heB) hc) _
    have h2 : p ^ (e + 1) ∣ u * F := (Nat.dvd_add_left h1).1 hd
    have h3 : p ^ (e + 1) ∣ F := (Nat.Coprime.pow_left _ hu).dvd_of_dvd_mul_left h2
    have := (hp.pow_dvd_iff_le_factorization hF).1 h3
    omega

theorem periodic_part (n : ℕ) (hn : 12 < n) (h12 : ¬ 12 ∣ n) :
    smooth3 (fib n) = smooth3 (fib (n - 12)) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 12 := ⟨n - 12, by omega⟩
  rw [Nat.add_sub_cancel]
  have hr : ¬ 12 ∣ r := by omega
  have hF : fib r ≠ 0 := by
    have : 0 < r := by omega
    exact (Nat.fib_pos.mpr this).ne'
  have d := dvd_fib_iff r
  unfold smooth3
  rw [fib_add_twelve]
  rw [fact_shift (B := 4) Nat.prime_two (by norm_num) (by norm_num) (by norm_num) hF
      (by norm_num; exact fun h => hr (d.1.1 h)),
    fact_shift (B := 2) Nat.prime_three (by norm_num) (by norm_num) (by norm_num) hF
      (by norm_num; exact fun h => hr (d.2.1 h))]

/-- v_2(F_(2m)) = v_2(F_m) + 1 when 4 ∣ F_m. -/
lemma step_two {m : ℕ} (hm : 1 ≤ m) (h4 : 4 ∣ fib m) :
    (fib (2 * m)).factorization 2 = (fib m).factorization 2 + 1 := by
  set a := fib m
  set c := fib (m - 1)
  have hsucc : fib (m + 1) = c + a := Nat.fib_add_one (by omega)
  have h2m : fib (2 * m) = a * (a + 2 * c) := by
    rw [Nat.fib_two_mul, hsucc]; congr 1; omega
  have hcop : Nat.Coprime c a := by
    have := Nat.fib_coprime_fib_succ (m - 1)
    rwa [show m - 1 + 1 = m by omega] at this
  have hc : c % 2 = 1 := by
    by_contra hc
    have h2c : 2 ∣ c := by omega
    have h2a : 2 ∣ a := dvd_trans (by norm_num) h4
    have := Nat.le_of_dvd one_pos
      (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd h2c h2a : 2 ∣ 1)
    omega
  have ha0 : a ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
  have hL0 : a + 2 * c ≠ 0 := by omega
  rw [h2m, Nat.factorization_mul ha0 hL0, Finsupp.add_apply]
  congr 1
  apply fact_eq Nat.prime_two hL0
  · omega
  · obtain ⟨t, ht⟩ := h4; omega

/-- v_3(F_(3m)) = v_3(F_m) + 1 when 3 ∣ F_m. -/
lemma step_three {m : ℕ} (hm : 1 ≤ m) (h3 : 3 ∣ fib m) :
    (fib (3 * m)).factorization 3 = (fib m).factorization 3 + 1 := by
  set a := fib m
  set c := fib (m - 1)
  have hsucc : fib (m + 1) = c + a := Nat.fib_add_one (by omega)
  have h2m : fib (2 * m) = a * (a + 2 * c) := by
    rw [Nat.fib_two_mul, hsucc]; congr 1; omega
  have h2m1 : fib (2 * m + 1) = (c + a) ^ 2 + a ^ 2 := by
    rw [Nat.fib_two_mul_add_one, hsucc]
  have h3m : fib (3 * m) = a * (3 * c ^ 2 + 3 * a * c + 2 * a ^ 2) := by
    have := Nat.fib_add (2 * m) (m - 1)
    rw [show 2 * m + (m - 1) + 1 = 3 * m by omega, show m - 1 + 1 = m by omega, h2m, h2m1]
      at this
    rw [this]; ring
  have hcop : Nat.Coprime c a := by
    have := Nat.fib_coprime_fib_succ (m - 1)
    rwa [show m - 1 + 1 = m by omega] at this
  have hc3 : c % 3 ≠ 0 := by
    intro hc
    have h3c : 3 ∣ c := by omega
    have := Nat.le_of_dvd one_pos
      (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd h3c h3 : 3 ∣ 1)
    omega
  have ha0 : a ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
  set K := 3 * c ^ 2 + 3 * a * c + 2 * a ^ 2 with hK
  have hK0 : K ≠ 0 := by positivity
  obtain ⟨s, hs⟩ := h3
  have hKmod : K % 9 = 3 := by
    have hK' : K = 9 * (s * c + 2 * s ^ 2) + 3 * c ^ 2 := by rw [hK, hs]; ring
    have hc2 : (3 * c ^ 2) % 9 = 3 := by
      rw [show (9 : ℕ) = 3 * 3 by norm_num, Nat.mul_mod_mul_left, Nat.pow_mod]
      have : c % 3 = 1 ∨ c % 3 = 2 := by omega
      rcases this with h | h <;> rw [h]
    omega
  rw [h3m, Nat.factorization_mul ha0 hK0, Finsupp.add_apply]
  congr 1
  apply fact_eq Nat.prime_three hK0
  · omega
  · omega

/-- Multiplying the index by a number prime to p keeps v_p, given the p-step. -/
lemma coprime_index {p m u : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hu : Nat.Coprime u p)
    (hstep : (fib (p * m)).factorization p = (fib m).factorization p + 1) :
    (fib (m * u)).factorization p = (fib m).factorization p := by
  have hu0 : u ≠ 0 := by
    rintro rfl; simp at hu; exact hp.one_lt.ne' hu
  have hmu0 : fib (m * u) ≠ 0 := (Nat.fib_pos.mpr (Nat.mul_pos (by omega) (by omega))).ne'
  have hpm0 : fib (p * m) ≠ 0 := (Nat.fib_pos.mpr (Nat.mul_pos hp.pos (by omega))).ne'
  have hm0 : fib m ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
  apply fact_eq hp hmu0
  · exact dvd_trans (Nat.ordProj_dvd _ _) (fibdvd (Dvd.intro u rfl))
  · intro hd
    have h2 : p ^ ((fib m).factorization p + 1) ∣ fib (p * m) :=
      (hp.pow_dvd_iff_le_factorization hpm0).2 hstep.ge
    have hg : Nat.gcd (fib (m * u)) (fib (p * m)) = fib m := by
      rw [← Nat.fib_gcd]
      congr 1
      rw [mul_comm p m, Nat.gcd_mul_left, hu.gcd_eq_one, mul_one]
    have : p ^ ((fib m).factorization p + 1) ∣ Nat.gcd (fib (m * u)) (fib (p * m)) :=
      Nat.dvd_gcd hd h2
    rw [hg] at this
    have := (hp.pow_dvd_iff_le_factorization hm0).1 this
    omega

/-- v_p(F_(m p^j)) = v_p(F_m) + j, given p ∣ F_m (p = 3) or 4 ∣ F_m (p = 2). -/
lemma pow_index {p m : ℕ} (hm : 1 ≤ m) (q : ℕ) (hq : q ∣ fib m)
    (hstep : ∀ m', 1 ≤ m' → q ∣ fib m' → (fib (p * m')).factorization p =
      (fib m').factorization p + 1) (hp1 : 1 ≤ p) (j : ℕ) :
    (fib (m * p ^ j)).factorization p = (fib m).factorization p + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hpos : 1 ≤ m * p ^ j := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
    have hq' : q ∣ fib (m * p ^ j) := dvd_trans hq (fibdvd (Dvd.intro _ rfl))
    have := hstep (m * p ^ j) hpos hq'
    rw [show m * p ^ (j + 1) = p * (m * p ^ j) by ring, this, ih]; ring

lemma val_twelve (p : ℕ) (hp : p.Prime) (q : ℕ) (hq : q ∣ fib 12)
    (hstep : ∀ m', 1 ≤ m' → q ∣ fib m' → (fib (p * m')).factorization p =
      (fib m').factorization p + 1) (k : ℕ) (hk : 1 ≤ k) :
    (fib (12 * k)).factorization p = (fib 12).factorization p + k.factorization p := by
  have hk0 : k ≠ 0 := by omega
  set j := k.factorization p
  set u := k / p ^ j
  have hku : k = p ^ j * u := (Nat.ordProj_mul_ordCompl_eq_self k p).symm
  have hu : Nat.Coprime u p := (Nat.coprime_ordCompl hp hk0).symm
  have h1 : 1 ≤ 12 * p ^ j := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne_zero))
  have hq' : q ∣ fib (12 * p ^ j) := dvd_trans hq (fibdvd (Dvd.intro _ rfl))
  have hc := coprime_index hp h1 hu (hstep _ h1 hq')
  have hpw := pow_index (by norm_num : 1 ≤ 12) q hq hstep hp.one_lt.le j
  rw [hku, ← mul_assoc, hc, hpw]

theorem twelve_part (k : ℕ) (hk : 1 ≤ k) : smooth3 (fib (12 * k)) = 144 * smooth3 k := by
  have h2 := val_twelve 2 Nat.prime_two 4 (by decide)
    (fun m' hm' h => step_two hm' h) k hk
  have h3 := val_twelve 3 Nat.prime_three 3 (by decide)
    (fun m' hm' h => step_three hm' h) k hk
  have f2 : (fib 12).factorization 2 = 4 :=
    fact_eq Nat.prime_two (by decide) (by decide) (by decide)
  have f3 : (fib 12).factorization 3 = 2 :=
    fact_eq Nat.prime_three (by decide) (by decide) (by decide)
  unfold smooth3
  rw [h2, h3, f2, f3]
  ring

theorem A081320_conjecture :
    (∀ n, 12 < n → ¬ 12 ∣ n → smooth3 (fib n) = smooth3 (fib (n - 12))) ∧
    (∀ k, 1 ≤ k → smooth3 (fib (12 * k)) = 144 * smooth3 k) :=
  ⟨periodic_part, twelve_part⟩
