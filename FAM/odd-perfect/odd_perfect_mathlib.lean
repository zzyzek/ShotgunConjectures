import Mathlib

/-!
# Odd perfect numbers: elementary necessary conditions

Checked here (Mathlib, no `sorry`, no `native_decide`): for an odd perfect
number `N` (Mathlib's `Nat.Perfect`)

* `oddPerfect_mod_four`: `N % 4 = 1` (pairing of divisors `d`, `N/d`).
* `oddPerfect_mod_three`: `N % 3 ≠ 2` (same pairing modulo 3).
* `oddPerfect_even_exp`: a prime `q ≡ 3 (mod 4)` divides `N` to an even power.
* `oddPerfect_nine_dvd`: `3 ∣ N → 9 ∣ N`.
* `oddPerfect_touchard`: Touchard's congruence `N % 12 = 1 ∨ N % 36 = 9`.
* `oddPerfect_not_dvd_105`: `¬ 105 ∣ N` (Sylvester).
* `oddPerfect_three_primeFactors`: `3 ≤ N.primeFactors.card`.

Not checked here: Euler's form `N = p^α m^2` with `p ≡ α ≡ 1 (mod 4)` (proved
in formal-conjectures by AlphaProof, not used), Sylvester's bound of 4 or 5
distinct prime factors, and all larger computer-assisted bounds.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

theorem OddPerfect.sigma_eq_two_mul {N : ℕ} (hp : N.Perfect) : σ 1 N = 2 * N := by
  rw [sigma_one_apply]
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul hp.2).1 hp

/-- If every divisor pair `d, N/d` is distinct and sums to `0` modulo `m`,
then `m ∣ σ(N)`. -/
theorem OddPerfect.dvd_sigma_of_pairs {N m : ℕ}
    (hsq : ∀ d ∈ N.divisors, N / d ≠ d)
    (hsum : ∀ d ∈ N.divisors, m ∣ d + N / d) : m ∣ σ 1 N := by
  rw [← ZMod.natCast_eq_zero_iff, sigma_one_apply, Nat.cast_sum]
  refine Finset.sum_involution (fun d _ => N / d) ?_ ?_ ?_ ?_
  · intro d hd
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    exact hsum d hd
  · intro d hd _
    exact hsq d hd
  · intro d hd
    have h := Nat.mem_divisors.1 hd
    exact Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd h.1, h.2⟩
  · intro d hd
    have h := Nat.mem_divisors.1 hd
    exact Nat.div_div_self h.1 h.2

theorem OddPerfect.oddPerfect_mod_four {N : ℕ} (hodd : Odd N) (hp : N.Perfect) :
    N % 4 = 1 := by
  have hN := (Nat.odd_iff.1 hodd)
  by_contra hne
  have h3 : N % 4 = 3 := by omega
  have key : 4 ∣ σ 1 N := by
    apply dvd_sigma_of_pairs
    · intro d hd heq
      have h := Nat.mem_divisors.1 hd
      have hmul : d * (N / d) = N := Nat.mul_div_cancel' h.1
      rw [heq] at hmul
      have := Nat.mul_mod d d 4
      have : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases hd4 : d % 4 <;> omega
    · intro d hd
      have h := Nat.mem_divisors.1 hd
      have hmul : d * (N / d) = N := Nat.mul_div_cancel' h.1
      have h1 := Nat.mul_mod d (N / d) 4
      have h2 : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have h3' : (N / d) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rw [hmul] at h1
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod]
      interval_cases hd4 : d % 4 <;> interval_cases he4 : (N / d) % 4 <;> omega
  rw [sigma_eq_two_mul hp] at key
  omega

theorem OddPerfect.oddPerfect_mod_three {N : ℕ} (hp : N.Perfect) : N % 3 ≠ 2 := by
  intro h2
  have key : 3 ∣ σ 1 N := by
    apply dvd_sigma_of_pairs
    · intro d hd heq
      have h := Nat.mem_divisors.1 hd
      have hmul : d * (N / d) = N := Nat.mul_div_cancel' h.1
      rw [heq] at hmul
      have := Nat.mul_mod d d 3
      have : d % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases hd3 : d % 3 <;> omega
    · intro d hd
      have h := Nat.mem_divisors.1 hd
      have hmul : d * (N / d) = N := Nat.mul_div_cancel' h.1
      have h1 := Nat.mul_mod d (N / d) 3
      have h2' : d % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have h3' : (N / d) % 3 < 3 := Nat.mod_lt _ (by norm_num)
      rw [hmul] at h1
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod]
      interval_cases hd3 : d % 3 <;> interval_cases he3 : (N / d) % 3 <;> omega
  rw [sigma_eq_two_mul hp] at key
  omega

/-- `σ(q^(2j+1))` is divisible by `4` when `q ≡ 3 (mod 4)`. -/
theorem OddPerfect.four_dvd_sigma_odd_pow {q : ℕ} (hq : q.Prime) (h3 : q % 4 = 3) (j : ℕ) :
    4 ∣ σ 1 (q ^ (2 * j + 1)) := by
  rw [sigma_one_apply_prime_pow hq]
  induction j with
  | zero =>
    simp [Finset.sum_range_succ]
    omega
  | succ j ih =>
    have e : 2 * (j + 1) + 1 + 1 = (2 * j + 1 + 1) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
    have hsplit : q ^ (2 * j + 1 + 1) + q ^ (2 * j + 1 + 1 + 1) =
        q ^ (2 * j + 2) * (q + 1) := by ring
    rw [add_assoc, hsplit]
    exact dvd_add ih (Dvd.dvd.mul_left (by omega) _)

/-- Splitting off a prime power multiplies `σ`. -/
theorem OddPerfect.sigma_split {q e M : ℕ} (hq : q.Prime) (hM : ¬ q ∣ M) :
    σ 1 (q ^ e * M) = σ 1 (q ^ e) * σ 1 M :=
  isMultiplicative_sigma.map_mul_of_coprime
    (((Nat.Prime.coprime_iff_not_dvd hq).2 hM).pow_left e)

theorem OddPerfect.oddPerfect_even_exp {N q e M : ℕ} (hodd : Odd N) (hp : N.Perfect)
    (hq : q.Prime) (h3 : q % 4 = 3) (hN : N = q ^ e * M) (hM : ¬ q ∣ M) :
    Even e := by
  by_contra he
  obtain ⟨j, rfl⟩ := Nat.not_even_iff_odd.1 he
  have h4 := four_dvd_sigma_odd_pow hq h3 j
  have hs := sigma_eq_two_mul hp
  rw [hN, sigma_split hq hM] at hs
  have : 4 ∣ 2 * (q ^ (2 * j + 1) * M) := hs ▸ Dvd.dvd.mul_right h4 _
  have hN2 := (Nat.odd_iff.1 hodd)
  rw [← hN] at this
  omega

theorem OddPerfect.oddPerfect_nine_dvd {N : ℕ} (hodd : Odd N) (hp : N.Perfect) (h3 : 3 ∣ N) :
    9 ∣ N := by
  have hN0 : N ≠ 0 := hp.2.ne'
  obtain ⟨e, M, hM, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 3 (by norm_num)
  have he := oddPerfect_even_exp hodd hp Nat.prime_three (by norm_num) hN hM
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [hN, pow_zero, one_mul] at h3
    exact hM h3
  obtain ⟨k, rfl⟩ := he
  have : 2 ≤ k + k := by omega
  rw [hN]
  exact Dvd.dvd.mul_right (by
    have := Nat.pow_dvd_pow 3 this
    simpa using this) _

/-- Touchard (1953): an odd perfect number is `1 (mod 12)` or `9 (mod 36)`. -/
theorem OddPerfect.oddPerfect_touchard {N : ℕ} (hodd : Odd N) (hp : N.Perfect) :
    N % 12 = 1 ∨ N % 36 = 9 := by
  have h4 := oddPerfect_mod_four hodd hp
  have h3 := oddPerfect_mod_three hp
  by_cases hd : 3 ∣ N
  · have h9 := oddPerfect_nine_dvd hodd hp hd
    omega
  · omega

/-- Lower bound `p^k (p^2+p+1) ≤ σ(p^k) p^2` for `k ≥ 2`. -/
theorem OddPerfect.sigma_pow_lower_two {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    p ^ k * (p ^ 2 + p + 1) ≤ σ 1 (p ^ k) * p ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  have h : p ^ (j + 2) * (p ^ 2 + p + 1) = (p ^ j + p ^ (j + 1) + p ^ (j + 2)) * p ^ 2 := by
    ring
  rw [h]
  apply Nat.mul_le_mul_right
  omega

/-- Lower bound `p^k (p+1) ≤ σ(p^k) p` for `k ≥ 1`. -/
theorem OddPerfect.sigma_pow_lower_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    p ^ k * (p + 1) ≤ σ 1 (p ^ k) * p := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_succ]
  have h : p ^ (j + 1) * (p + 1) = (p ^ j + p ^ (j + 1)) * p := by ring
  rw [h]
  apply Nat.mul_le_mul_right
  omega

theorem OddPerfect.le_sigma_self {M : ℕ} (hM : M ≠ 0) : M ≤ σ 1 M := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self M hM)

theorem OddPerfect.not_prime_dvd_pow {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ¬ p ∣ q ^ k := by
  intro h
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h))

/-- Sylvester (1888): an odd perfect number is not divisible by `105`. -/
theorem OddPerfect.oddPerfect_not_dvd_105 {N : ℕ} (hodd : Odd N) (hp : N.Perfect) :
    ¬ 105 ∣ N := by
  intro h105
  have hN0 : N ≠ 0 := hp.2.ne'
  have p3 := Nat.prime_three
  have p5 : Nat.Prime 5 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  obtain ⟨a, N1, h3N1, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 3 (by norm_num)
  have hN10 : N1 ≠ 0 := by rintro rfl; simp at hN; exact hN0 hN
  obtain ⟨b, N2, h5N2, hN1⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN10 5 (by norm_num)
  have hN20 : N2 ≠ 0 := by rintro rfl; simp at hN1; exact hN10 hN1
  obtain ⟨c, M, h7M, hN2⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN20 7 (by norm_num)
  have hM0 : M ≠ 0 := by rintro rfl; simp at hN2; exact hN20 hN2
  -- divisibility of the cofactors
  have h3N2 : ¬ 3 ∣ N2 := fun h => h3N1 (hN1 ▸ Dvd.dvd.mul_left h _)
  have h3M : ¬ 3 ∣ M := fun h => h3N2 (hN2 ▸ Dvd.dvd.mul_left h _)
  have h5M : ¬ 5 ∣ M := fun h => h5N2 (hN2 ▸ Dvd.dvd.mul_left h _)
  -- exponents
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hN
    exact h3N1 (hN ▸ Dvd.dvd.trans (by norm_num) h105)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hN1
    have h5 : 5 ∣ 3 ^ a * N1 := hN ▸ Dvd.dvd.trans (by norm_num) h105
    rcases (Nat.Prime.dvd_mul p5).1 h5 with h | h
    · exact not_prime_dvd_pow p5 p3 (by norm_num) h
    · exact h5N2 (hN1 ▸ h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hN2
    have h7 : 7 ∣ 3 ^ a * (5 ^ b * N2) := hN1 ▸ hN ▸ Dvd.dvd.trans (by norm_num) h105
    rcases (Nat.Prime.dvd_mul p7).1 h7 with h | h
    · exact not_prime_dvd_pow p7 p3 (by norm_num) h
    rcases (Nat.Prime.dvd_mul p7).1 h with h | h
    · exact not_prime_dvd_pow p7 p5 (by norm_num) h
    · exact h7M (hN2 ▸ h)
  have hNfull : N = 3 ^ a * (5 ^ b * (7 ^ c * M)) := by rw [hN, hN1, hN2]
  have ha : Even a := oddPerfect_even_exp hodd hp p3 (by norm_num) hN h3N1
  have h7rest : ¬ 7 ∣ 3 ^ a * 5 ^ b * M := by
    intro h
    rcases (Nat.Prime.dvd_mul p7).1 h with h | h
    · rcases (Nat.Prime.dvd_mul p7).1 h with h | h
      · exact not_prime_dvd_pow p7 p3 (by norm_num) h
      · exact not_prime_dvd_pow p7 p5 (by norm_num) h
    · exact h7M h
  have hc : Even c := oddPerfect_even_exp hodd hp p7 (by norm_num)
    (by rw [hNfull]; ring) h7rest
  have ha2 : 2 ≤ a := by obtain ⟨t, rfl⟩ := ha; omega
  have hc2 : 2 ≤ c := by obtain ⟨t, rfl⟩ := hc; omega
  -- sigma of the product
  have hs := sigma_eq_two_mul hp
  have h5_7M : ¬ 5 ∣ 7 ^ c * M := by
    intro h
    rcases (Nat.Prime.dvd_mul p5).1 h with h | h
    · exact not_prime_dvd_pow p5 p7 (by norm_num) h
    · exact h5M h
  have h3_rest : ¬ 3 ∣ 5 ^ b * (7 ^ c * M) := by
    intro h
    rcases (Nat.Prime.dvd_mul p3).1 h with h | h
    · exact not_prime_dvd_pow p3 p5 (by norm_num) h
    rcases (Nat.Prime.dvd_mul p3).1 h with h | h
    · exact not_prime_dvd_pow p3 p7 (by norm_num) h
    · exact h3M h
  rw [hNfull, sigma_split p3 h3_rest, sigma_split p5 h5_7M, sigma_split p7 h7M] at hs
  have hA := sigma_pow_lower_two p3 ha2
  have hB := sigma_pow_lower_one p5 (Nat.one_le_iff_ne_zero.2 hb0)
  have hC := sigma_pow_lower_two p7 hc2
  have hMle := le_sigma_self hM0
  norm_num at hA hB hC
  set A := 3 ^ a
  set B := 5 ^ b
  set C := 7 ^ c
  set sA := σ 1 A
  set sB := σ 1 B
  set sC := σ 1 C
  set sM := σ 1 M
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hCpos : 0 < C := by positivity
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
  -- sA sB sC M ≤ 2 A B C M
  have h1 : sA * sB * sC * M ≤ 2 * (A * B * C) * M := by
    calc sA * sB * sC * M ≤ sA * (sB * (sC * sM)) := by
          rw [← mul_assoc, ← mul_assoc]; exact Nat.mul_le_mul_left _ hMle
      _ = 2 * (A * B * C) * M := by rw [hs]; ring
  have h2 : sA * sB * sC ≤ 2 * (A * B * C) := Nat.le_of_mul_le_mul_right h1 hMpos
  have h3 : A * 13 * (B * 6) * (C * 57) ≤ sA * 9 * (sB * 5) * (sC * 49) :=
    Nat.mul_le_mul (Nat.mul_le_mul hA hB) hC
  have hABC : 0 < A * B * C := by positivity
  nlinarith

/-- `σ(p^k) (p-1) < p^(k+1)`, in the form `σ(p^k) (p-1) ≤ p^k p`. -/
theorem OddPerfect.sigma_pow_mul_pred_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ k) * (p - 1) ≤ p ^ k * p := by
  rw [sigma_one_apply_prime_pow hp]
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  simp only [Nat.add_sub_cancel]
  have key : ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), (r + 1) ^ i) * r + 1 = (r + 1) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ (r + 1) (k + 1)]
      nlinarith [ih]
  have := key k
  rw [← pow_succ]
  omega

/-- Abundancy bound: `σ(N) ∏ (p-1) ≤ N ∏ p` over the prime factors of `N`. -/
theorem OddPerfect.sigma_mul_prod_pred_le {N : ℕ} (hN : N ≠ 0) :
    σ 1 N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have hs := isMultiplicative_sigma.multiplicative_factorization (σ 1) hN
  have hN' := Nat.prod_factorization_pow_eq_self hN
  rw [Finsupp.prod, Nat.support_factorization] at hs hN'
  calc σ 1 N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, (σ 1 (p ^ N.factorization p) * (p - 1)) := by
        rw [hs, Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := by
        apply Finset.prod_le_prod
        intro p hp
        exact sigma_pow_mul_pred_le (Nat.prime_of_mem_primeFactors hp) _
    _ = N * ∏ p ∈ N.primeFactors, p := by
        rw [Finset.prod_mul_distrib, hN']

/-- An odd perfect number has at least three distinct prime factors. -/
theorem OddPerfect.oddPerfect_three_primeFactors {N : ℕ} (hodd : Odd N) (hp : N.Perfect) :
    3 ≤ N.primeFactors.card := by
  have hN0 : N ≠ 0 := hp.2.ne'
  have hb := sigma_mul_prod_pred_le hN0
  rw [sigma_eq_two_mul hp] at hb
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have key : 2 * ∏ p ∈ N.primeFactors, (p - 1) ≤ ∏ p ∈ N.primeFactors, p := by
    have : N * (2 * ∏ p ∈ N.primeFactors, (p - 1)) ≤ N * ∏ p ∈ N.primeFactors, p := by
      calc N * (2 * ∏ p ∈ N.primeFactors, (p - 1))
          = 2 * N * ∏ p ∈ N.primeFactors, (p - 1) := by ring
        _ ≤ _ := hb
    exact Nat.le_of_mul_le_mul_left this hNpos
  have hodd' : ∀ p ∈ N.primeFactors, 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp'
    have hpr := Nat.prime_of_mem_primeFactors hp'
    have hdvd := Nat.dvd_of_mem_primeFactors hp'
    rcases hpr.eq_two_or_odd with h2 | h2
    · subst h2
      exact absurd ((Nat.odd_iff.1 hodd)) (by omega)
    · exact ⟨by have := hpr.two_le; omega, h2⟩
  by_contra hlt
  have hlt := Nat.lt_of_not_le hlt
  interval_cases hc : N.primeFactors.card
  · rw [Finset.card_eq_zero] at hc
    rw [hc] at key
    simp at key
  · obtain ⟨p, hpe⟩ := Finset.card_eq_one.1 hc
    rw [hpe] at key hodd'
    simp at key hodd'
    omega
  · obtain ⟨p, q, hpq, hpe⟩ := Finset.card_eq_two.1 hc
    rw [hpe] at key hodd'
    rw [Finset.prod_pair hpq, Finset.prod_pair hpq] at key
    have hp3 := hodd' p (by simp)
    have hq3 := hodd' q (by simp)
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at key
    rcases Nat.lt_or_gt_of_ne hpq with h | h
    · have hb4 : 4 ≤ b := by omega
      nlinarith
    · have ha4 : 4 ≤ a := by omega
      nlinarith

