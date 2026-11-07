import Mathlib
import OpenProblemsLib.BernoulliDen

/-!
# OEIS A131262: least k with A130654(k) = n is sigma(2^n) phi(2^n) = 2^(n-1) (2^(n+1) - 1)

Definitions (OEIS, with the Taylor coefficients in Bernoulli form).
* `tanCoeff k` : coefficient of x^(2k-1) in tan x, written as
  2^(2k) (2^(2k) - 1) |B_(2k)| / (2k)!  (k >= 1).
* `logsecCoeff k = tanCoeff k / (2k)` : coefficient of x^(2k) in log(1/cos x)
  (the series with derivative tan x and constant term 0).
* `A002430 k`, `A046990 k` : their numerators.
* `A130654 k` : the 2-adic valuation of A002430(k) / A046990(k) (OEIS formula
  A130654(n) = A007814(A092505(n)) by Karttunen; equal to the "exponent m with
  2^m = A092505(n)" whenever that ratio is a power of 2).

Main results.
* `A130654_eq` : A130654 k = min (s2 k - 1) (1 + v2 k) for k >= 1, s2 = binary digit sum.
* `A131262_isLeast` : for n >= 1 the least k >= 1 with A130654 k = n is 2^(n-1) (2^(n+1) - 1).
* `A131262_zero` : the least such k for n = 0 is 1.
* `kstar_sigma_phi` : 2^(n-1) (2^(n+1) - 1) = sigma(2^n) phi(2^n) = 2^(2n) - 2^n / 2 (n >= 1).

Checked: everything above from Mathlib's `bernoulli` and the shared library's
`bernoulli_den_mod4` (von Staudt-Clausen at p = 2).
Not checked: that the Taylor coefficient of tan x equals the Bernoulli form (classical,
e.g. Abramowitz-Stegun 4.3.67); that A092505 is always a power of 2 (not needed).
-/

open OpenProblemsLib.BernoulliDen

noncomputable def tanCoeff (k : ℕ) : ℚ :=
  2 ^ (2 * k) * (2 ^ (2 * k) - 1) * |bernoulli (2 * k)| / ((2 * k).factorial : ℚ)

noncomputable def logsecCoeff (k : ℕ) : ℚ := tanCoeff k / ((2 * k : ℕ) : ℚ)

noncomputable def A002430 (k : ℕ) : ℕ := (tanCoeff k).num.natAbs

noncomputable def A046990 (k : ℕ) : ℕ := (logsecCoeff k).num.natAbs

noncomputable def A130654 (k : ℕ) : ℤ :=
  padicValRat 2 ((A002430 k : ℚ) / (A046990 k : ℚ))

/-- Binary digit sum. -/
def s2 (k : ℕ) : ℕ := (Nat.digits 2 k).sum

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma s2_double (k : ℕ) : s2 (2 * k) = s2 k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp [Nat.mul_mod_right, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]

lemma s2_pow_mul (j m : ℕ) : s2 (2 ^ j * m) = s2 m := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, mul_comm (2 ^ j) 2, mul_assoc, s2_double, ih]

lemma s2_pow_sub_one (j : ℕ) : s2 (2 ^ j - 1) = j := by
  induction j with
  | zero => simp [s2]
  | succ j ih =>
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    unfold s2 at ih ⊢
    rw [Nat.digits_def' (by norm_num) (by omega)]
    have hm : (2 ^ (j + 1) - 1) % 2 = 1 := by omega
    have hd : (2 ^ (j + 1) - 1) / 2 = 2 ^ j - 1 := by omega
    rw [hm, hd, List.sum_cons, ih]; ring

/-- A number with binary digit sum s is at least 2^s - 1. -/
lemma pow_s2_le (m : ℕ) : 2 ^ s2 m ≤ m + 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [s2]
    · have h := ih (m / 2) (by omega)
      have hs : s2 m = m % 2 + s2 (m / 2) := by
        unfold s2; rw [Nat.digits_def' (by norm_num) hm, List.sum_cons]
      rw [hs, pow_add]
      have : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases this with h0 | h0 <;> rw [h0] <;> simp <;> omega

lemma s2_pos (k : ℕ) (hk : 0 < k) : 1 ≤ s2 k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hs : s2 k = k % 2 + s2 (k / 2) := by
      unfold s2; rw [Nat.digits_def' (by norm_num) hk, List.sum_cons]
    rw [hs]
    rcases (by omega : k % 2 = 1 ∨ (k % 2 = 0 ∧ 0 < k / 2)) with h | ⟨_, h⟩
    · omega
    · have := ih (k / 2) (by omega) h; omega

/-- 2-adic valuation of B_(2k) is -1 for k >= 1. -/
lemma bern_val (k : ℕ) (hk : 0 < k) : padicValRat 2 (bernoulli (2 * k)) = -1 := by
  have h4 := bernoulli_den_mod4 k hk
  set q := bernoulli (2 * k)
  have hden : padicValNat 2 q.den = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, q.den = 2 * (2 * m + 1) := ⟨q.den / 4, by omega⟩
    rw [hm, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by omega)]
  have hnum : padicValInt 2 q.num = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro h
    have h2 : (2 : ℕ) ∣ q.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; simpa using this
    have hc := q.reduced
    have h3 : (2 : ℕ) ∣ q.den := by omega
    have := Nat.dvd_one.mp ((Nat.dvd_gcd h2 h3).trans hc.gcd_eq_one.dvd)
    norm_num at this
  rw [padicValRat_def, hnum, hden]; norm_num

lemma bern_ne (k : ℕ) (hk : 0 < k) : bernoulli (2 * k) ≠ 0 := by
  intro h
  have := bernoulli_den_mod4 k hk
  rw [h] at this; simp at this

lemma abs_val (q : ℚ) : padicValRat 2 |q| = padicValRat 2 q := by
  rcases abs_choice q with h | h <;> rw [h]
  exact padicValRat.neg q

lemma fact_val (k : ℕ) :
    (padicValNat 2 (2 * k).factorial : ℤ) = 2 * k - s2 k := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) (2 * k)
  have hle := Nat.digit_sum_le 2 (2 * k)
  have hs : (Nat.digits 2 (2 * k)).sum = s2 k := s2_double k
  rw [hs] at h hle
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
  rw [h]; push_cast [hle]; ring

lemma two_pow_sub_one_cast (k : ℕ) : ((2 : ℚ) ^ (2 * k) - 1) = ((2 ^ (2 * k) - 1 : ℕ) : ℚ) := by
  rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring

lemma odd_val (k : ℕ) (hk : 0 < k) : padicValNat 2 (2 ^ (2 * k) - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  have h2 : 2 ∣ 2 ^ (2 * k) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
  omega

lemma tan_ne (k : ℕ) (hk : 0 < k) : tanCoeff k ≠ 0 := by
  unfold tanCoeff
  have h1 : ((2 : ℚ) ^ (2 * k) - 1) ≠ 0 := by
    rw [two_pow_sub_one_cast]
    have : 1 < 2 ^ (2 * k) := Nat.one_lt_two_pow (by omega)
    exact_mod_cast (by omega : 2 ^ (2 * k) - 1 ≠ 0)
  have h2 : |bernoulli (2 * k)| ≠ 0 := abs_ne_zero.mpr (bern_ne k hk)
  have h3 : ((2 * k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  positivity

/-- 2-adic valuation of the tan coefficient: s2(k) - 1. -/
lemma tan_val (k : ℕ) (hk : 0 < k) : padicValRat 2 (tanCoeff k) = s2 k - 1 := by
  unfold tanCoeff
  have h0 : (2 : ℚ) ^ (2 * k) ≠ 0 := by positivity
  have h1 : ((2 : ℚ) ^ (2 * k) - 1) ≠ 0 := by
    rw [two_pow_sub_one_cast]
    have : 1 < 2 ^ (2 * k) := Nat.one_lt_two_pow (by omega)
    exact_mod_cast (by omega : 2 ^ (2 * k) - 1 ≠ 0)
  have h2 : |bernoulli (2 * k)| ≠ 0 := abs_ne_zero.mpr (bern_ne k hk)
  have h3 : ((2 * k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hs2 : padicValRat 2 (2 : ℚ) = 1 := by simpa using padicValRat.self (p := 2) (by norm_num)
  rw [padicValRat.div (by positivity) h3, padicValRat.mul (by positivity) h2,
    padicValRat.mul h0 h1, padicValRat.pow, hs2, abs_val,
    bern_val k hk, two_pow_sub_one_cast, ← padicValRat_of_nat, odd_val k hk,
    ← padicValRat_of_nat, fact_val]
  push_cast; ring

/-- 2-adic valuation of a numerator: max (v2 q) 0. -/
lemma num_val (q : ℚ) :
    (padicValNat 2 q.num.natAbs : ℤ) = max (padicValRat 2 q) 0 := by
  have hdef := padicValRat_def 2 q
  have hn : padicValInt 2 q.num = padicValNat 2 q.num.natAbs := rfl
  by_cases hd : padicValNat 2 q.den = 0
  · rw [hdef, hd, hn]; simp
  · have h3 : (2 : ℕ) ∣ q.den := dvd_of_one_le_padicValNat (by omega)
    have hnum : padicValNat 2 q.num.natAbs = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h2
      have := Nat.dvd_one.mp ((Nat.dvd_gcd h2 h3).trans q.reduced.gcd_eq_one.dvd)
      norm_num at this
    rw [hdef, hn, hnum]
    have : (0 : ℤ) < padicValNat 2 q.den := by exact_mod_cast Nat.pos_of_ne_zero hd
    simp only [Nat.cast_zero, zero_sub]; omega

lemma A130654_eq (k : ℕ) (hk : 0 < k) :
    A130654 k = min ((s2 k : ℤ) - 1) (1 + padicValNat 2 k) := by
  have ht := tan_ne k hk
  have h2k : ((2 * k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * k ≠ 0)
  have hc : logsecCoeff k ≠ 0 := div_ne_zero ht h2k
  have hv2k : padicValRat 2 ((2 * k : ℕ) : ℚ) = 1 + padicValNat 2 k := by
    rw [← padicValRat_of_nat, padicValNat.mul (by norm_num) (by omega),
      padicValNat.self (by norm_num)]; push_cast; ring
  have hcv : padicValRat 2 (logsecCoeff k) = s2 k - 1 - (1 + padicValNat 2 k) := by
    unfold logsecCoeff; rw [padicValRat.div ht h2k, tan_val k hk, hv2k]
  have ha : A002430 k ≠ 0 := by
    unfold A002430; simpa using Rat.num_ne_zero.mpr ht
  have hb : A046990 k ≠ 0 := by
    unfold A046990; simpa using Rat.num_ne_zero.mpr hc
  unfold A130654
  rw [padicValRat.div (by exact_mod_cast ha) (by exact_mod_cast hb),
    ← padicValRat_of_nat, ← padicValRat_of_nat]
  unfold A002430 A046990
  rw [num_val _, num_val _, tan_val k hk, hcv]
  have : (1 : ℤ) ≤ s2 k := by exact_mod_cast s2_pos k hk
  omega

/-- The candidate k* = 2^(n-1) (2^(n+1) - 1). -/
def kstar (n : ℕ) : ℕ := 2 ^ (n - 1) * (2 ^ (n + 1) - 1)

lemma kstar_pos (n : ℕ) : 0 < kstar n := by
  unfold kstar
  have : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
  exact Nat.mul_pos (by positivity) (by omega)

lemma A130654_kstar (n : ℕ) (hn : 1 ≤ n) : A130654 (kstar n) = n := by
  rw [A130654_eq _ (kstar_pos n)]
  unfold kstar
  rw [s2_pow_mul, s2_pow_sub_one]
  have hodd : padicValNat 2 (2 ^ (n + 1) - 1) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    have h2 : 2 ∣ 2 ^ (n + 1) := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    omega
  have : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow, hodd]
  push_cast; omega

lemma ge_kstar (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (h : A130654 k = n) : kstar n ≤ k := by
  rw [A130654_eq k hk] at h
  have hv : n - 1 ≤ padicValNat 2 k := by omega
  have hs : n + 1 ≤ s2 k := by omega
  obtain ⟨m, rfl⟩ := (padicValNat_dvd_iff_le (p := 2) (by omega)).mpr hv
  rw [s2_pow_mul] at hs
  have hm := pow_s2_le m
  have : 2 ^ (n + 1) ≤ 2 ^ s2 m := Nat.pow_le_pow_right (by norm_num) hs
  unfold kstar
  exact Nat.mul_le_mul_left _ (by omega)

theorem A131262_isLeast (n : ℕ) (hn : 1 ≤ n) :
    IsLeast {k : ℕ | 1 ≤ k ∧ A130654 k = n} (2 ^ (n - 1) * (2 ^ (n + 1) - 1)) :=
  ⟨⟨kstar_pos n, A130654_kstar n hn⟩, fun k hk => ge_kstar n k hn hk.1 hk.2⟩

theorem A131262_zero : IsLeast {k : ℕ | 1 ≤ k ∧ A130654 k = 0} 1 := by
  refine ⟨⟨le_rfl, ?_⟩, fun k hk => hk.1⟩
  rw [A130654_eq 1 (by norm_num)]
  simp [s2]

theorem kstar_sigma_phi (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n - 1) * (2 ^ (n + 1) - 1) = ArithmeticFunction.sigma 1 (2 ^ n) * Nat.totient (2 ^ n) ∧
    2 ^ (n - 1) * (2 ^ (n + 1) - 1) = 2 ^ (2 * n) - 2 ^ n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hg : ∑ i ∈ Finset.range (m + 1 + 1), (2 : ℕ) ^ i = 2 ^ (m + 2) - 1 := by
    have := Nat.geomSum_eq (m := 2) (le_refl 2) (m + 2)
    simpa using this
  have h1 : 1 ≤ 2 ^ (m + 2) := Nat.one_le_two_pow
  refine ⟨?_, ?_⟩
  · rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, hg,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp [mul_comm]
  · have e1 : 2 ^ (2 * (m + 1)) = 2 ^ m * 2 ^ (m + 2) := by rw [← pow_add]; ring_nf
    have e2 : 2 ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ]; simp
    simp only [show m + 1 - 1 = m from rfl, show m + 1 + 1 = m + 2 from rfl, e1, e2,
      Nat.mul_sub, mul_one]

