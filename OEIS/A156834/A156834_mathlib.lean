import Mathlib

/-
OEIS A156834 = A156348 * A000010 and A156833 = A054525 * A156348 * [1,2,3,...].
Conjecture (both entries): for n > 1, a(n) = n iff n is prime.

Definitions (as in the entries).
* `T n k` = A156348(n, k) = C(n/k - 2 + k, k - 1) if k | n, else 0 (written
  C(n/k + k - 2, k - 1), the same number since n/k + k >= 2).
* `Mu n k` = A054525(n, k) = mu(n/k) if k | n, else 0.
* `a834 n` = sum_{k=1..n} T n k * phi k (row n of A156348 times phi).
* `a833 n` = sum_{j=1..n} Mu n j * sum_{k=1..n} T j k * k (the matrix products).

Main theorems.
* `A156834_conj : 1 < n -> (a834 n = n <-> n.Prime)`.
  Route: a834 n = sum_{k | n} phi(k) C(n/k + k - 2, k - 1) (`a834_eq`); each
  binomial is >= 1, sum_{k | n} phi(k) = n, and a divisor 1 < k < n makes its
  binomial >= k >= 2.
* `A156833_conj : 1 < n -> (a833 n = n <-> n.Prime)`.
  Route: a833 n = sum_{k | n} k * I k (n/k) (`a833_eq`), with
  I k M = sum_{e | M} mu(M/e) C(e + k - 2, k - 1). I 1 M = 0 for M != 1
  (`I_one`), I k 1 = 1 (`I_at_one`), I k M > 0 for k >= 2 (`I_pos`):
  (k-1)! C(e + k - 2, k - 1) is the rising factorial e(e+1)...(e+k-2), a
  polynomial in e with natural coefficients and leading coefficient 1
  (Mathlib's `ascPochhammer`), so (k-1)! I k M is a nonnegative combination of
  the Jordan sums J r M = sum_{e | M} mu(M/e) e^r, which are >= 0, and > 0 for
  r >= 1 (`J_nonneg`, `J_pos`, via multiplicativity and
  J r (p^(b+1)) = p^((b+1) r) - p^(b r)).

Not checked in this file: agreement of `a834`, `a833` with the OEIS data terms
(certificate/check.py compares the definitions with the data, n = 1..51).
-/

namespace A156834

open Finset ArithmeticFunction

/-- Jordan-type sum J r M = Σ_{e ∣ M} μ(M/e) e^r. -/
def J (r M : ℕ) : ℤ := ∑ e ∈ M.divisors, moebius (M / e) * (e : ℤ) ^ r

def Fj (r : ℕ) : ArithmeticFunction ℤ := moebius * (pow r : ArithmeticFunction ℕ)

lemma Fj_apply (r M : ℕ) : Fj r M = J r M := by
  unfold Fj J
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => moebius a * ((pow r : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) b)]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
  simp [pow_apply, he0]

lemma Fj_mult (r : ℕ) : (Fj r).IsMultiplicative := by
  unfold Fj; exact
    isMultiplicative_moebius.mul isMultiplicative_pow.natCast

lemma J_prime_pow (r p b : ℕ) (hp : p.Prime) :
    J r (p ^ (b + 1)) = ((p : ℤ) ^ (b + 1)) ^ r - ((p : ℤ) ^ b) ^ r := by
  unfold J
  rw [Nat.divisors_prime_pow hp, Finset.sum_map, Finset.sum_range_succ, Finset.sum_range_succ]
  have hz : ∑ t ∈ range b, moebius (p ^ (b + 1) / p ^ t) * ((p ^ t : ℕ) : ℤ) ^ r = 0 := by
    refine Finset.sum_eq_zero (fun t ht => ?_)
    have htb : t < b := Finset.mem_range.mp ht
    rw [Nat.pow_div (by omega) hp.pos, moebius_apply_prime_pow hp (by omega)]
    simp; omega
  simp only [Function.Embedding.coeFn_mk] at hz ⊢
  rw [hz, Nat.pow_div (by omega) hp.pos, Nat.pow_div (by omega) hp.pos,
    show b + 1 - b = 1 by omega, Nat.sub_self, pow_one, pow_zero,
    moebius_apply_prime hp, moebius_apply_one]
  push_cast; ring

lemma J_nonneg (r M : ℕ) (hM : M ≠ 0) : 0 ≤ J r M := by
  rw [← Fj_apply, (Fj_mult r).multiplicative_factorization _ hM]
  refine Finset.prod_nonneg (fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  obtain ⟨b, hb⟩ : ∃ b, M.factorization p = b + 1 :=
    ⟨M.factorization p - 1, by
      have := Finsupp.mem_support_iff.mp hp; omega⟩
  dsimp only
  rw [hb, Fj_apply, J_prime_pow r p b hpp, sub_nonneg]
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hpp.one_le) (by omega)) r

lemma J_pos (r M : ℕ) (hr : 1 ≤ r) (hM : M ≠ 0) : 0 < J r M := by
  rw [← Fj_apply, (Fj_mult r).multiplicative_factorization _ hM]
  refine Finset.prod_pos (fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  obtain ⟨b, hb⟩ : ∃ b, M.factorization p = b + 1 :=
    ⟨M.factorization p - 1, by
      have := Finsupp.mem_support_iff.mp hp; omega⟩
  dsimp only
  rw [hb, Fj_apply, J_prime_pow r p b hpp, sub_pos]
  exact pow_lt_pow_left₀ (pow_lt_pow_right₀ (by exact_mod_cast hpp.one_lt) (by omega)) (by positivity) (by omega)


/-- A156348(n, k): C(n/k - 2 + k, k - 1) if k ∣ n, else 0. -/
def T (n k : ℕ) : ℕ := if k ∣ n then (n / k + k - 2).choose (k - 1) else 0

/-- A054525(n, k): μ(n/k) if k ∣ n, else 0. -/
def Mu (n k : ℕ) : ℤ := if k ∣ n then moebius (n / k) else 0

/-- A156834 = A156348 * A000010 (row n of the triangle times φ). -/
def a834 (n : ℕ) : ℕ := ∑ k ∈ Icc 1 n, T n k * Nat.totient k

/-- A156833 = A054525 * A156348 * [1, 2, 3, ...]. -/
def a833 (n : ℕ) : ℤ := ∑ j ∈ Icc 1 n, Mu n j * ∑ k ∈ Icc 1 n, (T j k : ℤ) * k

lemma divisors_sub_Icc {j n : ℕ} (hjn : j ≤ n) : j.divisors ⊆ Icc 1 n := by
  intro k hk
  have := Nat.mem_divisors.mp hk
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hk, (Nat.divisor_le hk).trans hjn⟩

lemma a834_eq (n : ℕ) :
    a834 n = ∑ k ∈ n.divisors, (n / k + k - 2).choose (k - 1) * Nat.totient k := by
  unfold a834
  rw [← Finset.sum_subset (divisors_sub_Icc le_rfl)]
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    simp [T, Nat.dvd_of_mem_divisors hk]
  · intro k hk hkn
    have hn : n ≠ 0 := by have := Finset.mem_Icc.mp hk; omega
    simp [T, Nat.mem_divisors, hn] at hkn ⊢
    simp [hkn]

/-- The comment of A156834: for n > 1, a(n) = n iff n is prime. -/
theorem A156834_conj (n : ℕ) (hn : 1 < n) : a834 n = n ↔ n.Prime := by
  rw [a834_eq]
  have hge : ∀ k ∈ n.divisors, Nat.totient k ≤ (n / k + k - 2).choose (k - 1) * Nat.totient k := by
    intro k hk
    have hk1 := Nat.pos_of_mem_divisors hk
    have hq : 1 ≤ n / k := Nat.div_pos (Nat.divisor_le hk) hk1
    have : 0 < (n / k + k - 2).choose (k - 1) := Nat.choose_pos (by omega)
    exact Nat.le_mul_of_pos_left _ this
  constructor
  · intro h
    by_contra hnp
    obtain ⟨k, hkn, hk1, hkn'⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
    have hkd : k ∈ n.divisors := Nat.mem_divisors.mpr ⟨hkn, by omega⟩
    have hq : 2 ≤ n / k := by
      rcases hkn with ⟨c, rfl⟩
      rw [Nat.mul_div_cancel_left _ (by omega)]
      by_contra hc
      interval_cases c <;> omega
    have hlt : Nat.totient k < (n / k + k - 2).choose (k - 1) * Nat.totient k := by
      have h2 : k ≤ (n / k + k - 2).choose (k - 1) := by
        calc k = (k).choose (k - 1) := by
              rw [Nat.choose_symm_of_eq_add (show k = (k - 1) + 1 by omega), Nat.choose_one_right]
          _ ≤ (n / k + k - 2).choose (k - 1) := Nat.choose_le_choose (k - 1) (by omega)
      have hphi : 0 < Nat.totient k := Nat.totient_pos.mpr (by omega)
      calc Nat.totient k < 2 * Nat.totient k := by omega
        _ ≤ (n / k + k - 2).choose (k - 1) * Nat.totient k :=
          Nat.mul_le_mul_right (Nat.totient k) (by omega : 2 ≤ (n / k + k - 2).choose (k - 1))
    have := Finset.sum_lt_sum hge ⟨k, hkd, hlt⟩
    rw [Nat.sum_totient] at this
    omega
  · intro hp
    rw [Nat.Prime.divisors hp, Finset.sum_pair (by omega)]
    have h1 : 1 + n - 2 = n - 1 := by omega
    simp [Nat.totient_prime hp, Nat.div_self hp.pos, h1]
    omega

/-- I k M = Σ_{e ∣ M} μ(M/e) C(e + k - 2, k - 1). -/
def I (k M : ℕ) : ℤ := ∑ e ∈ M.divisors, moebius (M / e) * ((e + k - 2).choose (k - 1) : ℤ)

lemma a833_eq1 (n : ℕ) :
    a833 n = ∑ j ∈ n.divisors, moebius (n / j) *
      ∑ k ∈ j.divisors, ((j / k + k - 2).choose (k - 1) : ℤ) * k := by
  unfold a833
  rw [← Finset.sum_subset (divisors_sub_Icc le_rfl)]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjn := Nat.divisor_le hj
    rw [show Mu n j = moebius (n / j) by simp [Mu, Nat.dvd_of_mem_divisors hj]]
    congr 1
    rw [← Finset.sum_subset (divisors_sub_Icc hjn)]
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      simp [T, Nat.dvd_of_mem_divisors hk]
    · intro k hk hkj
      have hj0 : j ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hj)
      simp [Nat.mem_divisors, hj0] at hkj
      simp [T, hkj]
  · intro j hj hjn
    have hn : n ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
    simp [Nat.mem_divisors, hn] at hjn
    simp [Mu, hjn]

lemma a833_eq (n : ℕ) : a833 n = ∑ k ∈ n.divisors, (k : ℤ) * I k (n / k) := by
  rw [a833_eq1]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := n.divisors) (s' := fun k => n.divisors.filter (k ∣ ·))]
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    have hkn : k ∣ n := Nat.dvd_of_mem_divisors hk
    have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hk).2
    unfold I
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun j => j / k) (fun e => k * e) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Nat.mem_divisors] at hj ⊢
      obtain ⟨⟨hjn, -⟩, hkj⟩ := hj
      refine ⟨Nat.div_dvd_div hkj hjn, ?_⟩
      exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hkn) hk0)
    · intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
      obtain ⟨hen, -⟩ := he
      refine ⟨⟨?_, hn0⟩, Dvd.intro e rfl⟩
      obtain ⟨c, hc⟩ := hen
      exact ⟨c, by rw [mul_assoc, ← hc, Nat.mul_div_cancel' hkn]⟩
    · intro j hj
      simp only [Finset.mem_filter] at hj
      exact Nat.mul_div_cancel' hj.2
    · intro e he
      exact Nat.mul_div_cancel_left e hk0
    · intro j hj
      simp only [Finset.mem_filter] at hj
      obtain ⟨e, rfl⟩ := hj.2
      rw [Nat.mul_div_cancel_left e hk0, Nat.div_div_eq_div_mul]
      ring
  · intro j k
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hjn, hn⟩, hkj, hj⟩
      exact ⟨⟨⟨hjn, hn⟩, hkj⟩, hkj.trans hjn, hn⟩
    · rintro ⟨⟨⟨hjn, hn⟩, hkj⟩, -, -⟩
      exact ⟨⟨hjn, hn⟩, hkj, by rintro rfl; simp at hjn; exact hn hjn⟩

lemma I_one (M : ℕ) (hM : M ≠ 1) : I 1 M = 0 := by
  unfold I
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [Nat.sum_div_divisors M (fun d => moebius d), ← coe_mul_zeta_apply, moebius_mul_coe_zeta]
  exact one_apply_ne hM

lemma I_at_one (k : ℕ) (hk : 1 ≤ k) : I k 1 = 1 := by
  unfold I
  simp [show 1 + k - 2 = k - 1 by omega]

lemma I_pos (k M : ℕ) (hk : 2 ≤ k) (hM : M ≠ 0) : 0 < I k M := by
  set m := k - 1 with hm
  have key : ((m.factorial : ℕ) : ℤ) * I k M =
      ∑ r ∈ range (m + 1), ((ascPochhammer ℕ m).coeff r : ℤ) * J r M := by
    unfold I J
    rw [Finset.mul_sum]
    have hterm : ∀ e ∈ M.divisors,
        ((m.factorial : ℕ) : ℤ) * (moebius (M / e) * ((e + k - 2).choose (k - 1) : ℤ)) =
        ∑ r ∈ range (m + 1), ((ascPochhammer ℕ m).coeff r : ℤ) * (moebius (M / e) * (e : ℤ) ^ r) := by
      intro e he
      have he0 : 0 < e := Nat.pos_of_mem_divisors he
      have h1 : e.ascFactorial m = m.factorial * (e + k - 2).choose (k - 1) := by
        rw [Nat.ascFactorial_eq_factorial_mul_choose', show e + m - 1 = e + k - 2 by omega]
      have h2 : ((e.ascFactorial m : ℕ) : ℤ) =
          ∑ r ∈ range (m + 1), ((ascPochhammer ℕ m).coeff r : ℤ) * (e : ℤ) ^ r := by
        rw [← ascPochhammer_nat_eq_ascFactorial, Polynomial.eval_eq_sum_range' (n := m + 1)]
        · push_cast; rfl
        · rw [ascPochhammer_natDegree]; omega
      rw [show ((m.factorial : ℕ) : ℤ) * (moebius (M / e) * ((e + k - 2).choose (k - 1) : ℤ)) =
          moebius (M / e) * ((m.factorial * (e + k - 2).choose (k - 1) : ℕ) : ℤ) by push_cast; ring,
        ← h1, h2, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => by rw [Finset.mul_sum])
  have hlead : (ascPochhammer ℕ m).coeff m = 1 := by
    have h := monic_ascPochhammer (S := ℕ) m
    rw [Polynomial.Monic, Polynomial.leadingCoeff, ascPochhammer_natDegree] at h
    exact h
  have hsum : 0 < ∑ r ∈ range (m + 1), ((ascPochhammer ℕ m).coeff r : ℤ) * J r M := by
    have hnn : ∀ r ∈ range (m + 1), 0 ≤ ((ascPochhammer ℕ m).coeff r : ℤ) * J r M :=
      fun r _ => mul_nonneg (by positivity) (J_nonneg r M hM)
    calc (0 : ℤ) < ((ascPochhammer ℕ m).coeff m : ℤ) * J m M := by
          rw [hlead]; simpa using J_pos m M (by omega) hM
      _ ≤ _ := Finset.single_le_sum hnn (Finset.self_mem_range_succ m)
  rw [← key] at hsum
  by_contra h
  have h := not_lt.mp h
  have : ((m.factorial : ℕ) : ℤ) * I k M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
  omega

lemma I_nonneg (k M : ℕ) (hM : M ≠ 1) (hM0 : M ≠ 0) : 0 ≤ I k M := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · have h0 : I 0 M = I 1 M := by unfold I; simp
      rw [h0, I_one M hM]
    · rw [I_one M hM]
  · exact (I_pos k M hk hM0).le

/-- The comment of A156833: for n > 1, a(n) = n iff n is prime. -/
theorem A156833_conj (n : ℕ) (hn : 1 < n) : a833 n = n ↔ n.Prime := by
  rw [a833_eq]
  have hn0 : n ≠ 0 := by omega
  have hsplit : ∑ k ∈ n.divisors, (k : ℤ) * I k (n / k) =
      n + ∑ k ∈ n.properDivisors, (k : ℤ) * I k (n / k) := by
    rw [← Nat.cons_self_properDivisors hn0, Finset.sum_cons, Nat.div_self (by omega),
      I_at_one n (by omega)]
    ring
  rw [hsplit]
  have hnn : ∀ k ∈ n.properDivisors, 0 ≤ (k : ℤ) * I k (n / k) := by
    intro k hk
    obtain ⟨hkn, hlt⟩ := Nat.mem_properDivisors.mp hk
    have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hkn (by omega)
    have hq : 1 < n / k := by
      rcases hkn with ⟨c, rfl⟩
      rw [Nat.mul_div_cancel_left _ hk0]
      by_contra hc; interval_cases c <;> omega
    exact mul_nonneg (by positivity) (I_nonneg k (n / k) (by omega) (by omega))
  constructor
  · intro h
    by_contra hnp
    obtain ⟨k, hkn, hk1, hkn'⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
    have hkp : k ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hkn, hkn'⟩
    have hq : 1 < n / k := by
      rcases hkn with ⟨c, rfl⟩
      rw [Nat.mul_div_cancel_left _ (by omega)]
      by_contra hc; interval_cases c <;> omega
    have hpos : 0 < (k : ℤ) * I k (n / k) :=
      mul_pos (by exact_mod_cast (by omega : 0 < k)) (I_pos k (n / k) hk1 (by omega))
    have := Finset.sum_pos' hnn ⟨k, hkp, hpos⟩
    omega
  · intro hp
    rw [Nat.Prime.properDivisors hp]
    simp [I_one n (by omega)]
