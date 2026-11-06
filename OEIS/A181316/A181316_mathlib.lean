import Mathlib
import OpenProblemsLib.Dwork

/-
OEIS A181316 (P. D. Hanna, 2010): g.f. exp(Σ_{n≥1} 2((3^n-1)/2)^(n-1) x^n/n).
Conjecture: exp(Σ_{n≥1} (q-1)((q^n-1)/(q-1))^(n-1) x^n/n) is an integer series for all
integers q > 1.

Definitions.
* `bq q n = (q-1) * ((q^n - 1)/(q - 1))^(n-1)` (ℤ division, exact; `div_eq_c`).
* `c q n = 1 + q + ... + q^(n-1)`.
* `expCoeff b n`: coefficients of exp(Σ b(n) x^n/n), given by A(0) = 1 and
  (n+1) A(n+1) = Σ_{j=0..n} b(j+1) A(n-j), over ℚ.

Main theorems.
* `A181316_conjecture (q) (2 ≤ q) n : ∃ z : ℤ, expCoeff (bq q) n = z`.
* `A181316_int`: the case q = 3 (the entry's own series).

Route.
* `LG_b`: the Gauss congruence b(m p^a) ≡ b(m p^(a-1)) (mod p^a) for every prime p, with
  N = M p: if p ∤ c(M) and p ∤ q-1, then c(N) ≡ c(M) (from q^N ≡ q^M, `pow_gauss`) and
  c(M)^(N-M) ≡ 1 (mod p^a); if p ∤ c(M) and p | q-1, then p ∤ M, so a = 1 and both terms are
  ≡ 0 (mod p); if p | c(M) (then p | c(N), `c_split`), both terms are ≡ 0 (mod p^a) by size of
  the exponents, except p = 2, a = 2, M = 2, where 4 | (q-1)(q+1).
* `dwork`, `expCoeff_int_of_euler`, `expCoeff`, `LGp`, `pow_gauss` (Gauss congruences give an
  Euler product Π (1 - x^d)^(-c(d)) with integer exponents): from the library module
  lib/OpenProblemsLib/Dwork.lean (namespace `OpenProblemsLib.Dwork`).
Not checked here: that `expCoeff` is the OEIS "exp(...)" (the recurrence is the standard
characterisation); the data match is checked by certificate/check.py only.
-/

namespace A181316

open PowerSeries OpenProblemsLib.Dwork


/-! ## the sequence (q-1) [n]_q^(n-1) -/

/-- `c q n = 1 + q + ... + q^(n-1)`. -/
def c (q : ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, q ^ i

/-- The OEIS summand: `b q n = (q-1) * ((q^n - 1)/(q - 1))^(n-1)`. -/
def bq (q : ℤ) (n : ℕ) : ℤ := (q - 1) * ((q ^ n - 1) / (q - 1)) ^ (n - 1)

theorem c_mul (q : ℤ) (n : ℕ) : c q n * (q - 1) = q ^ n - 1 := geom_sum_mul q n

theorem div_eq_c (q : ℤ) (hq : 2 ≤ q) (n : ℕ) : (q ^ n - 1) / (q - 1) = c q n := by
  rw [← c_mul]; exact Int.mul_ediv_cancel _ (by omega)

theorem bq_eq (q : ℤ) (hq : 2 ≤ q) (n : ℕ) : bq q n = (q - 1) * c q n ^ (n - 1) := by
  rw [bq, div_eq_c q hq]

theorem c_split (q : ℤ) (hq : 2 ≤ q) (M p : ℕ) : c q (M * p) = c q M * c (q ^ M) p := by
  have h1 := c_mul q (M * p)
  have h2 := c_mul q M
  have h3 := c_mul (q ^ M) p
  have hq1 : q - 1 ≠ 0 := by omega
  have h4 : (q ^ M) ^ p = q ^ (M * p) := (pow_mul q M p).symm
  apply mul_right_cancel₀ hq1
  linear_combination h1 - c (q ^ M) p * h2 - h3 - h4

theorem c_one (q : ℤ) : c q 1 = 1 := by simp [c]

theorem c_sub_self_dvd (q : ℤ) (M : ℕ) : (q - 1) ∣ c q M - M := by
  have : c q M - M = ∑ i ∈ Finset.range M, (q ^ i - 1) := by
    simp [c, Finset.sum_sub_distrib]
  rw [this]
  exact Finset.dvd_sum (fun i _ => by simpa using sub_dvd_pow_sub_pow q 1 i)

theorem two_pow_ge (a : ℕ) (ha : 3 ≤ a) : a + 1 ≤ 2 ^ (a - 1) := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases Nat.lt_or_ge a 3 with h | h
    · interval_cases a <;> simp_all
    · have := ih h
      rw [show a + 1 - 1 = (a - 1) + 1 by omega, pow_succ]; omega

theorem LG_b (q : ℤ) (hq : 2 ≤ q) (p : ℕ) (hp : p.Prime) :
    LGp p (fun n => (q - 1) * c q n ^ (n - 1)) := by
  intro a m ha
  simp only
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0; simp
  set M := m * p ^ (a - 1) with hMdef
  have hN : m * p ^ a = M * p := by
    rw [hMdef, mul_assoc, ← pow_succ, show a - 1 + 1 = a by omega]
  rw [hN]
  have hp2 := hp.two_le
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hMp : M ≤ M * p := Nat.le_mul_of_pos_right _ (by omega)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsplit := c_split q hq M p
  by_cases hc : (p : ℤ) ∣ c q M
  · have hcN : (p : ℤ) ∣ c q (M * p) := hsplit ▸ dvd_mul_of_dvd_left hc _
    have hM2 : 2 ≤ M := by
      by_contra h
      have : M = 1 := by omega
      rw [this, c_one] at hc
      exact hpz.not_dvd_one hc
    have hNa : a ≤ M * p - 1 := by
      have : a < p ^ a := Nat.lt_pow_self (by omega)
      have : p ^ a ≤ M * p := by rw [← hN]; exact Nat.le_mul_of_pos_left _ hm0
      omega
    have hbN : (p : ℤ) ^ a ∣ (q - 1) * c q (M * p) ^ (M * p - 1) :=
      dvd_mul_of_dvd_right ((pow_dvd_pow _ hNa).trans (pow_dvd_pow_of_dvd hcN _)) _
    have hbM : (p : ℤ) ^ a ∣ (q - 1) * c q M ^ (M - 1) := by
      by_cases hMa : a ≤ M - 1
      · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hMa).trans (pow_dvd_pow_of_dvd hc _)) _
      · -- the only case: p = 2, a = 2, M = 2
        have hpa : p ^ (a - 1) ≤ M := Nat.le_mul_of_pos_left _ hm0
        have hspec : p = 2 ∧ a = 2 ∧ M = 2 := by
          rcases Nat.lt_or_ge a 3 with h3 | h3
          · interval_cases a
            · omega
            · have hMle : M ≤ 2 := by omega
              have hmp : m * p = M := by rw [hMdef]; simp
              have hmle : m * 2 ≤ m * p := Nat.mul_le_mul_left m hp2
              have hm_1 : m = 1 := by nlinarith
              subst hm_1
              refine ⟨by omega, rfl, by omega⟩
          · have h1 := two_pow_ge a h3
            have h2 : 2 ^ (a - 1) ≤ p ^ (a - 1) := Nat.pow_le_pow_left hp2 _
            omega
        obtain ⟨rfl, rfl, hM⟩ := hspec
        rw [hM] at hc ⊢
        have hc2 : c q 2 = 1 + q := by simp [c, Finset.sum_range_succ]
        rw [hc2] at hc
        have h2 : (2 : ℤ) ∣ q - 1 := by
          have : q - 1 = (1 + q) - 2 := by ring
          rw [this]; exact dvd_sub (by exact_mod_cast hc) (dvd_refl _)
        rw [hc2]
        push_cast
        simpa [pow_two] using mul_dvd_mul h2 (show (2 : ℤ) ∣ (1 + q) ^ (2 - 1) by simpa using hc)
    exact dvd_sub hbN hbM
  · by_cases hq1 : (p : ℤ) ∣ q - 1
    · have ha1 : a = 1 := by
        by_contra h
        have hpM : (p : ℤ) ∣ (M : ℤ) := by
          rw [hMdef]; push_cast
          exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _
        exact hc ((dvd_sub_comm.mp (hq1.trans (c_sub_self_dvd q M))) |> fun h => by
          have := dvd_sub hpM h; simpa using this)
      subst ha1
      rw [pow_one, ← mul_sub]
      exact dvd_mul_of_dvd_left hq1 _
    · have hcop1 : IsCoprime ((p : ℤ) ^ a) (q - 1) :=
        (hpz.coprime_iff_not_dvd.mpr hq1).pow_left
      have hcop2 : IsCoprime ((p : ℤ) ^ a) (c q M) :=
        (hpz.coprime_iff_not_dvd.mpr hc).pow_left
      have h1 : (p : ℤ) ^ a ∣ c q (M * p) - c q M := by
        have g := pow_gauss p hp q a m ha
        rw [hN, ← hMdef] at g
        have e : q ^ (M * p) - q ^ M = (c q (M * p) - c q M) * (q - 1) := by
          rw [sub_mul, c_mul, c_mul]; ring
        rw [e] at g
        exact hcop1.dvd_of_dvd_mul_right g
      have h2 : (p : ℤ) ^ a ∣ c q M ^ (M * p - M) - 1 := by
        have g := pow_gauss p hp (c q M) a m ha
        rw [hN, ← hMdef] at g
        have e : c q M ^ (M * p) - c q M ^ M = c q M ^ M * (c q M ^ (M * p - M) - 1) := by
          rw [mul_sub, ← pow_add, show M + (M * p - M) = M * p by omega]; ring
        rw [e] at g
        exact (hcop2.pow_right).dvd_of_dvd_mul_left g
      have e : (q - 1) * c q (M * p) ^ (M * p - 1) - (q - 1) * c q M ^ (M - 1) =
          (q - 1) * ((c q (M * p) ^ (M * p - 1) - c q M ^ (M * p - 1)) +
            c q M ^ (M - 1) * (c q M ^ (M * p - M) - 1)) := by
        rw [mul_sub (c q M ^ (M - 1)), ← pow_add, show M - 1 + (M * p - M) = M * p - 1 by omega]
        ring
      rw [e]
      exact dvd_mul_of_dvd_right (dvd_add (h1.trans (sub_dvd_pow_sub_pow _ _ _))
        (dvd_mul_of_dvd_right h2 _)) _

/-- The conjecture of A181316: exp(Σ (q-1) ((q^n-1)/(q-1))^(n-1) x^n/n) is an integer series
for every integer q ≥ 2. -/
theorem A181316_conjecture (q : ℤ) (hq : 2 ≤ q) (n : ℕ) : ∃ z : ℤ, expCoeff (bq q) n = z := by
  have hb : bq q = fun n => (q - 1) * c q n ^ (n - 1) := funext (bq_eq q hq)
  rw [hb]
  exact expCoeff_int_of_euler _ _ (dwork _ (fun p hp => LG_b q hq p hp)) n

/-- A181316 itself (q = 3): exp(Σ 2 ((3^n-1)/2)^(n-1) x^n/n) has integer coefficients. -/
theorem A181316_int (n : ℕ) : ∃ z : ℤ, expCoeff (bq 3) n = z := A181316_conjecture 3 (by norm_num) n
