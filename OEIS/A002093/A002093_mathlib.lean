import Mathlib
import OpenProblemsLib.PNTApps

/-
OEIS-A002093 (Mathlib). Highly abundant numbers: n ≥ 1 with σ(m) < σ(n) for all 1 ≤ m < n.
Conjecture (b) (J. Coleman, 2013): for every k there is A with k ∣ a(n) for all a(n) > A.

Main theorem `A002093_partB`: for every k ≥ 1 there is A such that every highly abundant
n > A is divisible by k. `A002093_primePow` is the prime-power case q^e.

Proof (a variant of the README argument that needs no density of i log q - j log r).
Suppose v_q(n) = a < e. Put G = σ(q^(e-1)), k = 2qG. Pick a prime s ≠ q and j ≥ 1 with
s^j ∣ n, s^j large and (s-1)·s^(v_s(n)-j) ≥ 4qG: either n has a large prime factor s (j = 1),
or n is smooth, and then some s has a large exponent b (j = b - 4qG). By the prime number
theorem (PNT+ `prime_between`) there is a prime Q with k s^j < (k+1) q Q and q Q < s^j,
Q ∉ {q, s}. Then m = n q Q / s^j < n and σ(m) ≥ σ(n) (`ha_key`), so n is not highly abundant.

Part (a) (every highly abundant number > 10 is practical) is not formalised here: it is cited
from D. Eppstein (blog, 2015-02-26).
Outside Lean: part (a). The prime number theorem input is the vendored PNT+ (lib/PNTPlus),
checked in Lean.
-/

open ArithmeticFunction


/-- OEIS A002093: n ≥ 1 with σ(m) < σ(n) for every 1 ≤ m < n. -/
def IsHighlyAbundant (n : ℕ) : Prop :=
  0 < n ∧ ∀ m, 0 < m → m < n → sigma 1 m < sigma 1 n

lemma ha_sig_pp {p i : ℕ} (hp : p.Prime) : sigma 1 (p ^ i) = ∑ t ∈ Finset.range (i + 1), p ^ t :=
  sigma_one_apply_prime_pow hp

lemma ha_sig_succ {p i : ℕ} (hp : p.Prime) : sigma 1 (p ^ (i + 1)) = p * sigma 1 (p ^ i) + 1 := by
  rw [ha_sig_pp hp, ha_sig_pp hp, Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma ha_sig_split {p c j : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ (c + (j + 1))) = p ^ (j + 1) * sigma 1 (p ^ c) + sigma 1 (p ^ j) := by
  rw [ha_sig_pp hp, ha_sig_pp hp, ha_sig_pp hp, show c + (j + 1) + 1 = (j + 1) + (c + 1) by ring,
    Finset.sum_range_add, Finset.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun t _ => by rw [pow_add]

lemma ha_sig_geom {p j : ℕ} (hp : p.Prime) : (p - 1) * sigma 1 (p ^ j) + 1 = p ^ (j + 1) := by
  have h := geom_sum_mul_add (p - 1) (j + 1)
  rw [Nat.sub_add_cancel hp.one_le] at h
  rw [ha_sig_pp hp, mul_comm]
  exact h

lemma ha_sig_ge {p i : ℕ} (hp : p.Prime) : p ^ i ≤ sigma 1 (p ^ i) := by
  rw [ha_sig_pp hp]
  exact Finset.single_le_sum (f := fun t => p ^ t) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_succ_self i))

lemma ha_sig_mono {p i i' : ℕ} (hp : p.Prime) (h : i ≤ i') : sigma 1 (p ^ i) ≤ sigma 1 (p ^ i') := by
  rw [ha_sig_pp hp, ha_sig_pp hp]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

lemma ha_sig_mul {x y : ℕ} (h : x.Coprime y) : sigma 1 (x * y) = sigma 1 x * sigma 1 y :=
  isMultiplicative_sigma.map_mul_of_coprime h

lemma ha_cop_pow {p x i : ℕ} (hp : p.Prime) (h : ¬ p ∣ x) : (p ^ i).Coprime x :=
  Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).2 h)

lemma ha_not_dvd_pow {p r i : ℕ} (hp : p.Prime) (hr : r.Prime) (h : p ≠ r) : ¬ p ∣ r ^ i := by
  intro hd
  exact h ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow hd))

/-- The arithmetic core: with A = σ(q^a) ≤ G, S' = σ(s^c'), T = σ(s^(j-1)), the
replacement q^a s^(c'+j) Q^c → q^(a+1) s^c' Q^(c+1) does not lower σ. -/
lemma ha_core_ineq (q Q s sj A G S' T : ℕ) (hq : 1 ≤ q) (hA : A ≤ G)
    (h1 : 2 * q * G * sj < (2 * q * G + 1) * (q * Q)) (hT : (s - 1) * T + 1 = sj)
    (hS : 4 * q * G * Q ≤ (s - 1) * S' * Q) :
    A * (sj * S' + T) ≤ (q * A + 1) * S' * Q := by
  rcases Nat.eq_zero_or_pos G with hG | hG
  · subst hG; simp at hA; subst hA; simp
  have hsj : sj < 2 * q * Q := by
    by_contra hc
    push Not at hc
    have h0 : 2 * q * G * (2 * (q * Q)) ≤ 2 * q * G * sj :=
      Nat.mul_le_mul_left _ (by rw [← mul_assoc]; exact hc)
    have hK : 0 < 2 * q * G := by positivity
    generalize 2 * q * G = K at h0 h1 hK
    generalize q * Q = X at h0 h1
    have e1 : (K + 1) * X = K * X + X := by ring
    have e2 : K * (2 * X) = 2 * (K * X) := by ring
    have : X ≤ K * X := Nat.le_mul_of_pos_left X hK
    omega
  have hT2 : 2 * G * T ≤ S' * Q := by
    have e1 : (s - 1) * (2 * G * T) < (s - 1) * (S' * Q) := by
      calc (s - 1) * (2 * G * T) = 2 * G * ((s - 1) * T) := by ring
        _ < 2 * G * sj := by apply Nat.mul_lt_mul_of_pos_left _ (by omega); omega
        _ ≤ 2 * G * (2 * q * Q) := Nat.mul_le_mul_left _ hsj.le
        _ = 4 * q * G * Q := by ring
        _ ≤ (s - 1) * S' * Q := hS
        _ = (s - 1) * (S' * Q) := by ring
    exact (Nat.lt_of_mul_lt_mul_left e1).le
  have hk : 0 < 2 * q * G := by positivity
  apply Nat.le_of_mul_le_mul_left _ hk
  have e2 : 2 * q * G * (A * (sj * S' + T)) ≤
      A * S' * ((2 * q * G + 1) * (q * Q)) + 2 * q * G * A * T := by
    have := Nat.mul_le_mul_left (A * S') h1.le
    nlinarith
  have e3 : A * q * Q * S' ≤ G * q * Q * S' := by
    apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ hA
  have e4 : 2 * q * G * A * T ≤ q * G * (S' * Q) := by
    calc 2 * q * G * A * T ≤ 2 * q * G * G * T := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ hA
      _ = q * G * (2 * G * T) := by ring
      _ ≤ q * G * (S' * Q) := Nat.mul_le_mul_left _ hT2
  nlinarith

/-- Key replacement: n = q^a s^b Q^c z → m = q^(a+1) s^(b-j) Q^(c+1) z. -/
lemma ha_key {q s Q a b c j e z : ℕ} (hq : q.Prime) (hs : s.Prime) (hQ : Q.Prime)
    (hqs : q ≠ s) (hqQ : q ≠ Q) (hsQ : s ≠ Q) (hqz : ¬ q ∣ z) (hsz : ¬ s ∣ z) (hQz : ¬ Q ∣ z)
    (hae : a < e) (hj : 1 ≤ j) (hjb : j ≤ b)
    (h1 : 2 * q * sigma 1 (q ^ (e - 1)) * s ^ j <
      (2 * q * sigma 1 (q ^ (e - 1)) + 1) * (q * Q))
    (h2 : q * Q < s ^ j) (h3 : 4 * q * sigma 1 (q ^ (e - 1)) ≤ (s - 1) * s ^ (b - j)) :
    q ^ (a + 1) * (s ^ (b - j) * (Q ^ (c + 1) * z)) < q ^ a * (s ^ b * (Q ^ c * z)) ∧
    sigma 1 (q ^ a * (s ^ b * (Q ^ c * z))) ≤
      sigma 1 (q ^ (a + 1) * (s ^ (b - j) * (Q ^ (c + 1) * z))) := by
  have hz : 0 < z := Nat.pos_of_ne_zero (by rintro rfl; exact hQz (dvd_zero _))
  obtain ⟨c', rfl⟩ : ∃ c', b = c' + j := ⟨b - j, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hbj : c' + (j' + 1) - (j' + 1) = c' := by omega
  rw [hbj] at h3 ⊢
  constructor
  · have hpos : 0 < q ^ a * (s ^ c' * (Q ^ c * z)) := by
      have := hq.pos; have := hs.pos; have := hQ.pos; positivity
    calc q ^ (a + 1) * (s ^ c' * (Q ^ (c + 1) * z))
        = (q * Q) * (q ^ a * (s ^ c' * (Q ^ c * z))) := by ring
      _ < s ^ (j' + 1) * (q ^ a * (s ^ c' * (Q ^ c * z))) := Nat.mul_lt_mul_of_pos_right h2 hpos
      _ = q ^ a * (s ^ (c' + (j' + 1)) * (Q ^ c * z)) := by ring
  · -- Split σ over the three prime powers and the cofactor z.
    have cQ : ∀ i, (Q ^ i).Coprime z := fun i => ha_cop_pow hQ hQz
    have cs : ∀ i i', (s ^ i).Coprime (Q ^ i' * z) := fun i i' =>
      ha_cop_pow hs (fun h => (Nat.Prime.dvd_mul hs).1 h |>.elim (ha_not_dvd_pow hs hQ hsQ) hsz)
    have cq : ∀ i i' i'', (q ^ i).Coprime (s ^ i' * (Q ^ i'' * z)) := fun i i' i'' =>
      ha_cop_pow hq (fun h => (Nat.Prime.dvd_mul hq).1 h |>.elim (ha_not_dvd_pow hq hs hqs)
        (fun h' => (Nat.Prime.dvd_mul hq).1 h' |>.elim (ha_not_dvd_pow hq hQ hqQ) hqz))
    rw [ha_sig_mul (cq _ _ _), ha_sig_mul (cs _ _), ha_sig_mul (cQ _), ha_sig_mul (cq _ _ _),
      ha_sig_mul (cs _ _), ha_sig_mul (cQ _), ha_sig_succ hq, ha_sig_succ hQ, ha_sig_split hs]
    set G := sigma 1 (q ^ (e - 1))
    set A := sigma 1 (q ^ a)
    set S' := sigma 1 (s ^ c')
    set T := sigma 1 (s ^ j')
    set C := sigma 1 (Q ^ c)
    set Z := sigma 1 z
    have hA : A ≤ G := ha_sig_mono hq (by omega)
    have hT : (s - 1) * T + 1 = s ^ (j' + 1) := ha_sig_geom hs
    have hS : 4 * q * G * Q ≤ (s - 1) * S' * Q := by
      apply Nat.mul_le_mul_right
      exact h3.trans (Nat.mul_le_mul_left _ (ha_sig_ge hs))
    have hc := ha_core_ineq q Q s (s ^ (j' + 1)) A G S' T hq.one_le hA h1 hT hS
    calc A * ((s ^ (j' + 1) * S' + T) * (C * Z))
        = (A * (s ^ (j' + 1) * S' + T)) * C * Z := by ring
      _ ≤ ((q * A + 1) * S' * Q) * C * Z := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ hc
      _ ≤ (q * A + 1) * (S' * ((Q * C + 1) * Z)) := by
          have : (q * A + 1) * S' * Q * C * Z + (q * A + 1) * S' * Z =
              (q * A + 1) * (S' * ((Q * C + 1) * Z)) := by ring
          omega

/-- Primes in short intervals (PNT): a prime Q > W with k N < (k+1) q Q and q Q < N. -/
lemma ha_exists_Q (k q W : ℕ) (hk : 0 < k) (hq : 0 < q) : ∃ Y, ∀ N, Y ≤ N →
    ∃ Q, Q.Prime ∧ k * N < (k + 1) * (q * Q) ∧ q * Q < N ∧ W < Q := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (prime_between (ε := 1 / (k : ℝ)) (by positivity))
  refine ⟨(⌈a⌉₊ + W + 1) * (q * (k + 1)), fun N hN => ?_⟩
  set x : ℝ := (N : ℝ) * k / (q * (k + 1)) with hx
  have hNR : ((⌈a⌉₊ + W + 1 : ℕ) : ℝ) * (q * (k + 1)) ≤ N := by exact_mod_cast hN
  have hd : (0 : ℝ) < q * (k + 1) := by positivity
  have hxl : ((⌈a⌉₊ + W + 1 : ℕ) : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ hd]
    have : (N : ℝ) ≤ N * k := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hk)
    linarith
  have hca : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
  push_cast at hxl
  obtain ⟨p, hp, hp1, hp2⟩ := ha x (by linarith)
  have hx2 : (1 + 1 / (k : ℝ)) * x = N / q := by
    rw [hx]; field_simp
  rw [hx2, lt_div_iff₀ hqR] at hp2
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · rw [hx, div_lt_iff₀ hd] at hp1
    have : ((k * N : ℕ) : ℝ) < ((k + 1) * (q * p) : ℕ) := by push_cast; nlinarith
    exact_mod_cast this
  · have : ((q * p : ℕ) : ℝ) < N := by push_cast; linarith
    exact_mod_cast this
  · have : (W : ℝ) < p := by have : (0 : ℝ) ≤ ⌈a⌉₊ := by positivity
                             linarith
    exact_mod_cast this

/-- A u ≠ 0 whose prime factors are all < X with exponents ≤ B satisfies u ≤ (X^B)^X. -/
lemma ha_smooth_bound (u X B : ℕ) (hu : u ≠ 0) (hX : 1 ≤ X)
    (h : ∀ p ∈ u.primeFactors, p < X ∧ u.factorization p ≤ B) : u ≤ (X ^ B) ^ X := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hu]
  rw [Finsupp.prod, Nat.support_factorization]
  calc ∏ p ∈ u.primeFactors, p ^ u.factorization p ≤ (X ^ B) ^ u.primeFactors.card := by
        apply Finset.prod_le_pow_card
        intro p hp
        obtain ⟨h1, h2⟩ := h p hp
        exact (Nat.pow_le_pow_left h1.le _).trans (Nat.pow_le_pow_right hX h2)
    _ ≤ (X ^ B) ^ X := by
        apply Nat.pow_le_pow_right (Nat.one_le_pow _ _ hX)
        calc u.primeFactors.card ≤ (Finset.range X).card := by
              apply Finset.card_le_card
              intro p hp; exact Finset.mem_range.2 (h p hp).1
          _ = X := Finset.card_range X

lemma ha_factorization_split {u s b w : ℕ} (hs : s.Prime) (hw : ¬ s ∣ w) (hu : u = s ^ b * w) :
    u.factorization s = b := by
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero _)
  rw [hu, Nat.factorization_mul (pow_ne_zero _ hs.ne_zero) hw0, Finsupp.add_apply,
    hs.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hw]
  rfl

/-- Prime-power case: q^e divides every sufficiently large highly abundant number. -/
theorem A002093_primePow (q e : ℕ) (hq : q.Prime) :
    ∃ A, ∀ n, IsHighlyAbundant n → A < n → q ^ e ∣ n := by
  set G := sigma 1 (q ^ (e - 1))
  set k := 2 * q * G
  set L := 4 * q * G
  have hG : 1 ≤ G := (Nat.one_le_pow _ _ hq.pos).trans (ha_sig_ge hq)
  have hk : 0 < k := Nat.mul_pos (Nat.mul_pos (by norm_num) hq.pos) hG
  obtain ⟨Y1, hY1⟩ := ha_exists_Q k q q hk hq.pos
  set X := Y1 + L + q + 2
  obtain ⟨Y2, hY2⟩ := ha_exists_Q k q X hk hq.pos
  set B := L + Y2 + e
  refine ⟨q ^ e * (X ^ B) ^ X, fun n hn hnA => ?_⟩
  by_contra hdiv
  have hn0 : n ≠ 0 := hn.1.ne'
  obtain ⟨a, u, hqu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 q hq.one_lt.ne'
  have hae : a < e := by
    by_contra hc; exact hdiv (Dvd.dvd.mul_right (Nat.pow_dvd_pow q (by omega)) _)
  have hu0 : u ≠ 0 := by rintro rfl; simp at hn0
  have huX : (X ^ B) ^ X < u := by
    by_contra hc
    push Not at hc
    have : q ^ a * u ≤ q ^ e * (X ^ B) ^ X :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hq.pos hae.le) hc
    omega
  -- Some prime s ∣ u is large or has a large exponent.
  have hX1 : 1 ≤ X := by omega
  obtain ⟨s, hsu, hsc⟩ : ∃ s ∈ u.primeFactors, X ≤ s ∨ B < u.factorization s := by
    by_contra hc
    push Not at hc
    exact absurd (ha_smooth_bound u X B hu0 hX1 hc) (not_le.2 huX)
  have hs : s.Prime := Nat.prime_of_mem_primeFactors hsu
  have hsd : s ∣ u := Nat.dvd_of_mem_primeFactors hsu
  have hqs : q ≠ s := by rintro rfl; exact hqu hsd
  obtain ⟨b, w, hsw, hub⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu0 s hs.one_lt.ne'
  have hb := ha_factorization_split hs hsw hub
  have hb1 : 1 ≤ b := by
    rw [← hb]; exact (hs.dvd_iff_one_le_factorization hu0).1 hsd
  -- Choose j and the prime Q.
  obtain ⟨j, Q, hj, hjb, hQ, h1, h2, hQq, hQs, h3⟩ : ∃ j Q, 1 ≤ j ∧ j ≤ b ∧ Q.Prime ∧
      k * s ^ j < (k + 1) * (q * Q) ∧ q * Q < s ^ j ∧ q ≠ Q ∧ s ≠ Q ∧
      4 * q * G ≤ (s - 1) * s ^ (b - j) := by
    by_cases hsX : X ≤ s
    · obtain ⟨Q, hQ, h1, h2, h4⟩ := hY1 (s ^ 1) (by rw [pow_one]; omega)
      refine ⟨1, Q, le_rfl, hb1, hQ, h1, h2, by omega, ?_, ?_⟩
      · rintro rfl; rw [pow_one] at h2; nlinarith [hq.two_le]
      · calc 4 * q * G ≤ s - 1 := by omega
          _ ≤ (s - 1) * s ^ (b - 1) := Nat.le_mul_of_pos_right _ (Nat.pow_pos hs.pos)
    · have hbB : B < b := by
        rcases hsc with h | h
        · exact absurd h hsX
        · rwa [hb] at h
      push Not at hsX
      have hj : Y2 ≤ s ^ (b - L) :=
        (show Y2 ≤ b - L by omega).trans
          ((Nat.lt_pow_self hs.one_lt).le)
      obtain ⟨Q, hQ, h1, h2, h4⟩ := hY2 (s ^ (b - L)) hj
      refine ⟨b - L, Q, by omega, by omega, hQ, h1, h2, by omega, by omega, ?_⟩
      rw [show b - (b - L) = L by omega]
      calc 4 * q * G = L := rfl
        _ ≤ s ^ L := (Nat.lt_pow_self hs.one_lt).le
        _ ≤ (s - 1) * s ^ L := Nat.le_mul_of_pos_left _ (by have := hs.two_le; omega)
  have hw0 : w ≠ 0 := by rintro rfl; exact hsw (dvd_zero _)
  obtain ⟨c, z, hQz, hwz⟩ := Nat.exists_eq_pow_mul_and_not_dvd hw0 Q hQ.one_lt.ne'
  have hzw : z ∣ w := ⟨Q ^ c, by rw [hwz, mul_comm]⟩
  have hzu : z ∣ u := hzw.trans ⟨s ^ b, by rw [hub, mul_comm]⟩
  have hsz : ¬ s ∣ z := fun h => hsw (h.trans hzw)
  have hqz : ¬ q ∣ z := fun h => hqu (h.trans hzu)
  have hkey := ha_key (e := e) (a := a) (c := c) hq hs hQ hqs hQq hQs hqz hsz hQz hae hj hjb h1 h2 h3
  rw [hub, hwz] at hn
  obtain ⟨hlt, hle⟩ := hkey
  have hm0 : 0 < q ^ (a + 1) * (s ^ (b - j) * (Q ^ (c + 1) * z)) := by
    have := hq.pos; have := hs.pos; have := hQ.pos
    have : 0 < z := Nat.pos_of_ne_zero (by rintro rfl; exact hQz (dvd_zero _))
    positivity
  exact absurd (hn.2 _ hm0 hlt) (not_lt.2 hle)

/-- Conjecture (b) of A002093: every k ≥ 1 divides all sufficiently large highly abundant
numbers. -/
theorem A002093_partB (k : ℕ) (hk : 0 < k) :
    ∃ A, ∀ n, IsHighlyAbundant n → A < n → k ∣ n := by
  induction k using Nat.recOnPosPrimePosCoprime with
  | prime_pow p i hp _ => exact A002093_primePow p i hp
  | zero => exact absurd hk (lt_irrefl 0)
  | one => exact ⟨0, fun n _ _ => one_dvd n⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨A1, h1⟩ := iha (by omega)
    obtain ⟨A2, h2⟩ := ihb (by omega)
    exact ⟨max A1 A2, fun n hn hlt =>
      hab.mul_dvd_of_dvd_of_dvd (h1 n hn (lt_of_le_of_lt (le_max_left _ _) hlt))
        (h2 n hn (lt_of_le_of_lt (le_max_right _ _) hlt))⟩

