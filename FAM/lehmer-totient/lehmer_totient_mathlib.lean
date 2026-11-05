import Mathlib

/-
Lehmer's totient problem (FAM-lehmer-totient), weaker results.

A Lehmer number is a composite n > 1 with φ(n) ∣ n - 1 (`IsLehmer`). None is known.
Checked here (Lean + Mathlib):
* `squarefree_of_isLehmer`, `odd_of_isLehmer`: a Lehmer number is squarefree and odd.
* `isCarmichael_of_isLehmer`: it is a Carmichael number (Korselt), so (Mathlib)
  `three_le_card_of_isLehmer`: it has at least 3 distinct prime factors.
* `prime_lt_of_isLehmer`: Pomerance's Lemma 3 (1977) specialised to a = 1. For a prime
  factor p of n, with A the product of the prime factors below p and k the number of
  prime factors at least p, p < k(A + 1).
* `le_bound_of_isLehmer`: with K distinct prime factors, n ≤ (2K)^(2^K - 1).
* `finite_isLehmer_card`: for each K, finitely many Lehmer numbers have K prime factors.
* `four_le_card_of_isLehmer`: a Lehmer number has at least 4 distinct prime factors.
Not checked: Pomerance's sharper bound n < K^(2^K) (it needs the bound p(n) ≤ K - 1 from
Norton and Grün), and the literature bounds (at least 14 or 15 prime factors).
-/

open Finset

/-- A counterexample to Lehmer's totient problem: composite n > 1 with φ(n) ∣ n - 1. -/
def IsLehmer (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime ∧ n.totient ∣ n - 1

lemma dvd_one_of_dvd_dvd_pred {d n : ℕ} (hn : 1 ≤ n) (h1 : d ∣ n) (h2 : d ∣ n - 1) :
    d ∣ 1 := by
  have h3 := Nat.dvd_sub h1 h2
  rwa [Nat.sub_sub_self hn] at h3

theorem squarefree_of_isLehmer {n : ℕ} (h : IsLehmer n) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have h2 : (p * p).totient = p * (p - 1) := by
    rw [← pow_two, Nat.totient_prime_pow hp (by norm_num)]
    simp
  have h1 : p ∣ n.totient :=
    (h2 ▸ dvd_mul_right p (p - 1)).trans (Nat.totient_dvd_of_dvd hpp)
  have h3 : p ∣ 1 :=
    dvd_one_of_dvd_dvd_pred h.1.le ((dvd_mul_right p p).trans hpp) (h1.trans h.2.2)
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

lemma two_lt_of_isLehmer {n : ℕ} (h : IsLehmer n) : 2 < n := by
  rcases Nat.lt_or_ge 2 n with h2 | h2
  · exact h2
  · exfalso
    have : n = 2 := by have := h.1; omega
    exact h.2.1 (this ▸ Nat.prime_two)

theorem odd_of_isLehmer {n : ℕ} (h : IsLehmer n) : Odd n := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have he := Nat.totient_even (two_lt_of_isLehmer h)
  have h3 : 2 ∣ 1 := dvd_one_of_dvd_dvd_pred h.1.le (even_iff_two_dvd.mp hodd)
    ((even_iff_two_dvd.mp he).trans h.2.2)
  omega

theorem isCarmichael_of_isLehmer {n : ℕ} (h : IsLehmer n) : n.IsCarmichael := by
  refine Nat.isCarmichael_iff_korselt.mpr
    ⟨two_lt_of_isLehmer h, h.2.1, squarefree_of_isLehmer h, fun p hp hpn => ?_⟩
  rw [← Nat.totient_prime hp]
  exact (Nat.totient_dvd_of_dvd hpn).trans h.2.2

theorem three_le_card_of_isLehmer {n : ℕ} (h : IsLehmer n) : 3 ≤ n.primeFactors.card :=
  (isCarmichael_of_isLehmer h).three_le_card_primeFactors

/-- n - 1 = φ(n) m with m ≥ 2 (m = 1 would make n prime). -/
lemma exists_mul_of_isLehmer {n : ℕ} (h : IsLehmer n) :
    ∃ m, 2 ≤ m ∧ n - 1 = n.totient * m := by
  obtain ⟨m, hm⟩ := h.2.2
  refine ⟨m, ?_, hm⟩
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · exfalso
    interval_cases m
    · have := h.1; simp at hm; omega
    · exact h.2.1 ((Nat.totient_eq_iff_prime (by have := h.1; omega)).mp (by simpa using hm.symm))
  · exact hm2

lemma totient_eq_prod_of_squarefree {n : ℕ} (hsq : Squarefree n) (hn : 0 < n) :
    n.totient = ∏ q ∈ n.primeFactors, (q - 1) := by
  have h := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h
  exact Nat.eq_of_mul_eq_mul_left hn (by rw [mul_comm]; exact h)

/-- Bernoulli-type inequality: (x+1)^k (x+1-k) ≤ x^k (x+1) for x ≥ 0. -/
lemma bernoulli_aux (x : ℤ) (hx : 0 ≤ x) :
    ∀ k : ℕ, (x + 1) ^ k * (x + 1 - k) ≤ x ^ k * (x + 1)
  | 0 => by simp
  | k + 1 => by
    have ih := bernoulli_aux x hx k
    have h1 : (x + 1) ^ k * ((x + 1) * (x - k)) ≤ (x + 1) ^ k * (x * (x + 1 - k)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have h2 : x * ((x + 1) ^ k * (x + 1 - k)) ≤ x * (x ^ k * (x + 1)) :=
      mul_le_mul_of_nonneg_left ih hx
    push_cast
    calc (x + 1) ^ (k + 1) * (x + 1 - (k + 1)) = (x + 1) ^ k * ((x + 1) * (x - k)) := by ring
      _ ≤ (x + 1) ^ k * (x * (x + 1 - k)) := h1
      _ = x * ((x + 1) ^ k * (x + 1 - k)) := by ring
      _ ≤ x * (x ^ k * (x + 1)) := h2
      _ = x ^ (k + 1) * (x + 1) := by ring

/-- If (A+1)(p-1)^k < A p^k (p ≥ 1), then p < k (A + 1). -/
lemma lt_of_pow_ineq {A p k : ℕ} (hp : 1 ≤ p)
    (h : (A + 1) * (p - 1) ^ k < A * p ^ k) : p < k * (A + 1) := by
  by_contra hc
  replace hc := not_lt.mp hc
  set x : ℤ := (p : ℤ) - 1 with hxdef
  have hx : 0 ≤ x := by
    have : (1 : ℤ) ≤ p := by exact_mod_cast hp
    rw [hxdef]; linarith
  have hpx : (p : ℤ) = x + 1 := by rw [hxdef]; ring
  have hcast : (((p - 1 : ℕ)) : ℤ) = x := by rw [hxdef]; push_cast [Nat.cast_sub hp]; ring
  have hZ : ((A : ℤ) + 1) * x ^ k < (A : ℤ) * (x + 1) ^ k := by
    have := (show (((A + 1) * (p - 1) ^ k : ℕ) : ℤ) < ((A * p ^ k : ℕ) : ℤ) by exact_mod_cast h)
    push_cast at this
    rw [hcast, hpx] at this
    exact this
  have hc' : (k : ℤ) * ((A : ℤ) + 1) ≤ x + 1 := by
    rw [← hpx]; exact_mod_cast hc
  have hb := bernoulli_aux x hx k
  have hP : 0 ≤ (x + 1) ^ k := by positivity
  have hA : (0 : ℤ) ≤ A := by positivity
  have ha : (A : ℤ) * (x + 1) ≤ ((A : ℤ) + 1) * (x + 1 - k) := by nlinarith
  have e1 := mul_le_mul_of_nonneg_left ha hP
  have e2 := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℤ) ≤ (A : ℤ) + 1)
  have e3 := mul_lt_mul_of_pos_right hZ (by linarith : (0 : ℤ) < x + 1)
  nlinarith

/-- Pomerance (1977), Lemma 3 with a = 1: each prime factor p of a Lehmer number satisfies
p < k (A + 1), where A is the product of the prime factors below p and k is the number of
prime factors at least p. -/
theorem prime_lt_of_isLehmer {n : ℕ} (h : IsLehmer n) {p : ℕ} (hp : p ∈ n.primeFactors) :
    p < (n.primeFactors.filter (fun q => ¬ q < p)).card *
      ((∏ q ∈ n.primeFactors.filter (fun q => q < p), q) + 1) := by
  have hsq := squarefree_of_isLehmer h
  have hn0 : 0 < n := by have := h.1; omega
  obtain ⟨m, hm2, hm⟩ := exists_mul_of_isLehmer h
  set S := n.primeFactors with hS
  set L := S.filter (fun q => q < p) with hL
  set U := S.filter (fun q => ¬ q < p) with hU
  set A := ∏ q ∈ L, q with hA
  set B := ∏ q ∈ U, q with hB
  set Fa := ∏ q ∈ L, (q - 1) with hFa
  set Fb := ∏ q ∈ U, (q - 1) with hFb
  set k := U.card with hk
  have hpr : ∀ q ∈ S, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hnAB : n = A * B := by
    rw [hA, hB, prod_filter_mul_prod_filter_not, hS, Nat.prod_primeFactors_of_squarefree hsq]
  have hφ : n.totient = Fa * Fb := by
    rw [hFa, hFb, prod_filter_mul_prod_filter_not, totient_eq_prod_of_squarefree hsq hn0]
  have hFaA : Fa ≤ A :=
    prod_le_prod (fun q _ => Nat.sub_le q 1)
  have hFa1 : 1 ≤ Fa := by
    apply Nat.one_le_iff_ne_zero.mpr
    rw [hFa, prod_ne_zero_iff]
    intro q hq
    have := (hpr q (mem_filter.mp hq).1).two_le
    omega
  have hA1 : 1 ≤ A := hFa1.trans hFaA
  have hpU : p ∈ U := mem_filter.mpr ⟨hp, lt_irrefl p⟩
  have hFbB : Fb < B := by
    apply prod_lt_prod_of_nonempty₀
    · intro q hq
      have := (hpr q (mem_filter.mp hq).1).two_le
      omega
    · intro q hq
      have := (hpr q (mem_filter.mp hq).1).two_le
      omega
    · exact ⟨p, hpU⟩
  have hp1 : 1 ≤ p := (hpr p hp).one_lt.le
  have hpow : B * (p - 1) ^ k ≤ Fb * p ^ k := by
    rw [hk, ← prod_const, ← prod_const, hB, hFb, ← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_le_prod
    intro q hq
    have hpq : p ≤ q := not_lt.mp (mem_filter.mp hq).2
    rw [Nat.mul_sub_one, Nat.sub_one_mul]
    exact Nat.sub_le_sub_left hpq _
  have hAB : A * B = Fa * Fb * m + 1 := by
    rw [← hφ, ← hm, ← hnAB]; omega
  have hgap : A + 1 ≤ m * Fa := by
    by_contra hc
    have hc' : m * Fa ≤ A := by omega
    have e1 := Nat.mul_le_mul_right Fb hc'
    have e2 := Nat.mul_le_mul_left A (show Fb + 1 ≤ B from hFbB)
    have hA_le : A ≤ 1 := by nlinarith
    have hA_eq : A = 1 := le_antisymm hA_le hA1
    have hFa_eq : Fa = 1 := le_antisymm (hA_eq ▸ hFaA) hFa1
    rw [hA_eq, hFa_eq] at hc'
    omega
  have hlt1 : (A + 1) * Fb < A * B := by
    have := Nat.mul_le_mul_right Fb hgap
    nlinarith
  have hlt2 : (A + 1) * Fb * p ^ k < A * B * p ^ k :=
    Nat.mul_lt_mul_of_pos_right hlt1 (pow_pos hp1 k)
  have hle3 : (A + 1) * (B * (p - 1) ^ k) ≤ (A + 1) * (Fb * p ^ k) :=
    Nat.mul_le_mul_left _ hpow
  have hlt4 : B * ((A + 1) * (p - 1) ^ k) < B * (A * p ^ k) := by
    have : B * ((A + 1) * (p - 1) ^ k) = (A + 1) * (B * (p - 1) ^ k) := by ring
    rw [this]
    calc (A + 1) * (B * (p - 1) ^ k) ≤ (A + 1) * (Fb * p ^ k) := hle3
      _ = (A + 1) * Fb * p ^ k := by ring
      _ < A * B * p ^ k := hlt2
      _ = B * (A * p ^ k) := by ring
  exact lt_of_pow_ineq hp1 (Nat.lt_of_mul_lt_mul_left hlt4)

/-- The product of the j smallest prime factors of a Lehmer number with K prime factors is
at most (2K)^(2^j - 1). -/
theorem prod_filter_lt_le {n : ℕ} (h : IsLehmer n) :
    ∀ j t : ℕ, (n.primeFactors.filter (fun q => q < t)).card = j →
      ∏ q ∈ n.primeFactors.filter (fun q => q < t), q ≤
        (2 * n.primeFactors.card) ^ (2 ^ j - 1) := by
  intro j
  induction j with
  | zero =>
    intro t ht
    rw [card_eq_zero] at ht
    rw [ht]
    simp
  | succ j ih =>
    intro t ht
    set S := n.primeFactors with hS
    set K := S.card with hK
    have hne : (S.filter (fun q => q < t)).Nonempty := by
      rw [← card_pos, ht]; omega
    set p := (S.filter (fun q => q < t)).max' hne with hpdef
    have hpF : p ∈ S.filter (fun q => q < t) := max'_mem _ hne
    have hpS : p ∈ S := (mem_filter.mp hpF).1
    have hpt : p < t := (mem_filter.mp hpF).2
    have hsplit : S.filter (fun q => q < t) = insert p (S.filter (fun q => q < p)) := by
      ext q
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hq, hqt⟩
        have hle : q ≤ p := le_max' _ q (mem_filter.mpr ⟨hq, hqt⟩)
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Or.inr ⟨hq, hlt⟩
        · exact Or.inl heq
      · rintro (heq | ⟨hq, hqp⟩)
        · exact heq ▸ ⟨hpS, hpt⟩
        · exact ⟨hq, lt_trans hqp hpt⟩
    have hpnot : p ∉ S.filter (fun q => q < p) := by simp
    have hcard : (S.filter (fun q => q < p)).card = j := by
      rw [hsplit, card_insert_of_notMem hpnot] at ht; omega
    have hAp := ih p hcard
    have hplt := prime_lt_of_isLehmer h hpS
    set A := ∏ q ∈ S.filter (fun q => q < p), q with hA
    have hkK : (S.filter (fun q => ¬ q < p)).card ≤ K := card_filter_le _ _
    have hA1 : 1 ≤ A := by
      apply Nat.one_le_iff_ne_zero.mpr
      rw [hA, prod_ne_zero_iff]
      intro q hq
      exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1).ne_zero
    have hp2 : p ≤ 2 * K * A := by
      have := Nat.mul_le_mul_right (A + 1) hkK
      nlinarith
    rw [hsplit, prod_insert hpnot]
    set X := (2 * K) ^ (2 ^ j - 1) with hX
    have e : 2 ^ (j + 1) - 1 = (2 ^ j - 1) + (2 ^ j - 1) + 1 := by
      have := Nat.one_le_two_pow (n := j)
      rw [pow_succ]; omega
    rw [e, pow_succ, pow_add]
    calc p * A ≤ 2 * K * A * A := Nat.mul_le_mul_right A hp2
      _ ≤ 2 * K * X * X := by
        have := Nat.mul_le_mul hAp hAp
        nlinarith
      _ = X * X * (2 * K) := by ring

/-- A Lehmer number with K distinct prime factors satisfies n ≤ (2K)^(2^K - 1). -/
theorem le_bound_of_isLehmer {n : ℕ} (h : IsLehmer n) :
    n ≤ (2 * n.primeFactors.card) ^ (2 ^ n.primeFactors.card - 1) := by
  have hall : n.primeFactors.filter (fun q => q < n + 1) = n.primeFactors := by
    apply filter_true_of_mem
    intro q hq
    exact Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors hq)
  have := prod_filter_lt_le h n.primeFactors.card (n + 1) (by rw [hall])
  rwa [hall, Nat.prod_primeFactors_of_squarefree (squarefree_of_isLehmer h)] at this

/-- For each K, only finitely many Lehmer numbers have exactly K distinct prime factors. -/
theorem finite_isLehmer_card (K : ℕ) :
    {n : ℕ | IsLehmer n ∧ n.primeFactors.card = K}.Finite := by
  apply (Set.finite_Iic ((2 * K) ^ (2 ^ K - 1))).subset
  rintro n ⟨h, hK⟩
  rw [Set.mem_Iic, ← hK]
  exact le_bound_of_isLehmer h

/-- Finite check behind the case of three prime factors x < y < z (Boolean form). -/
def check3 : Bool :=
  (List.range 6).all fun x => (List.range 12).all fun y => (List.range 56).all fun z =>
    !(decide (3 ≤ x) && decide (x < y) && decide (y < z) && decide (y < 2 * (x + 1)) &&
      decide (z < x * y + 1) && decide (z % x ≠ 0) &&
      decide ((x * y * z - 1) % ((x - 1) * (y - 1) * (z - 1)) = 0))

lemma check3_eq : check3 = true := by decide

lemma three_check {x y z : ℕ} (hx6 : x < 6) (hy12 : y < 12) (hz56 : z < 56) (h3 : 3 ≤ x)
    (hxy : x < y) (hyz : y < z) (hy : y < 2 * (x + 1)) (hz : z < x * y + 1) (hxz : ¬ x ∣ z) :
    ¬ ((x - 1) * (y - 1) * (z - 1) ∣ x * y * z - 1) := by
  intro hd
  have hc := check3_eq
  simp only [check3, List.all_eq_true, List.mem_range] at hc
  have := hc x hx6 y hy12 z hz56
  have hzx : z % x ≠ 0 := fun h0 => hxz (Nat.dvd_of_mod_eq_zero h0)
  simp [h3, hxy, hyz, hy, hz, hzx, Nat.mod_eq_zero_of_dvd hd] at this

lemma not_three_ordered {n x y z : ℕ} (h : IsLehmer n) (hxy : x < y) (hyz : y < z)
    (hS : n.primeFactors = {x, y, z}) : False := by
  have hxz : x < z := lt_trans hxy hyz
  have hx := prime_lt_of_isLehmer h (p := x) (by rw [hS]; simp)
  have hy := prime_lt_of_isLehmer h (p := y) (by rw [hS]; simp)
  have hz := prime_lt_of_isLehmer h (p := z) (by rw [hS]; simp)
  rw [hS] at hx hy hz
  have fLx : ({x, y, z} : Finset ℕ).filter (fun q => q < x) = ∅ := by
    ext q; simp; omega
  have fUx : ({x, y, z} : Finset ℕ).filter (fun q => ¬ q < x) = {x, y, z} := by
    ext q; simp; omega
  have fLy : ({x, y, z} : Finset ℕ).filter (fun q => q < y) = {x} := by
    ext q; simp; omega
  have fUy : ({x, y, z} : Finset ℕ).filter (fun q => ¬ q < y) = {y, z} := by
    ext q; simp; omega
  have fLz : ({x, y, z} : Finset ℕ).filter (fun q => q < z) = {x, y} := by
    ext q; simp; omega
  have fUz : ({x, y, z} : Finset ℕ).filter (fun q => ¬ q < z) = {z} := by
    ext q; simp; omega
  have c3 : ({x, y, z} : Finset ℕ).card = 3 :=
    card_eq_three.mpr ⟨x, y, z, hxy.ne, hxz.ne, hyz.ne, rfl⟩
  rw [fLx, fUx, c3, prod_empty] at hx
  rw [fLy, fUy, card_pair hyz.ne, prod_singleton] at hy
  rw [fLz, fUz, card_singleton, prod_pair hxy.ne] at hz
  have hsq := squarefree_of_isLehmer h
  have hn0 : 0 < n := by have := h.1; omega
  have hprod : n = x * y * z := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq, hS]
    simp [prod_insert, hxy.ne, hyz.ne, hxz.ne, mul_assoc]
  have htot : n.totient = (x - 1) * (y - 1) * (z - 1) := by
    rw [totient_eq_prod_of_squarefree hsq hn0, hS]
    simp [prod_insert, hxy.ne, hyz.ne, hxz.ne, mul_assoc]
  have hxp : x.Prime := Nat.prime_of_mem_primeFactors (by rw [hS]; simp)
  have hzp : z.Prime := Nat.prime_of_mem_primeFactors (by rw [hS]; simp)
  have hodd := odd_of_isLehmer h
  have hx3 : 3 ≤ x := by
    have h2 := hxp.two_le
    rcases Nat.lt_or_ge x 3 with hlt | hge
    · exfalso
      have hx2 : x = 2 := by omega
      have : 2 ∣ n := hx2 ▸ Nat.dvd_of_mem_primeFactors (by rw [hS]; simp)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    · exact hge
  have hxz' : ¬ x ∣ z := by
    intro hd
    rcases hzp.eq_one_or_self_of_dvd x hd with h1 | h1
    · omega
    · omega
  have hdvd := h.2.2
  rw [htot, hprod] at hdvd
  have hz' : z < x * y + 1 := by omega
  have hy' : y < 2 * (x + 1) := hy
  have hx6 : x < 6 := by omega
  have hy12 : y < 12 := by omega
  have hz56 : z < 56 := by nlinarith
  exact three_check hx6 hy12 hz56 hx3 hxy hyz hy' hz' hxz' hdvd

/-- A Lehmer number has at least 4 distinct prime factors. -/
theorem four_le_card_of_isLehmer {n : ℕ} (h : IsLehmer n) : 4 ≤ n.primeFactors.card := by
  have h3 := three_le_card_of_isLehmer h
  by_contra hc
  have hc3 : n.primeFactors.card = 3 := by omega
  obtain ⟨x, y, z, hxy, hxz, hyz, hS⟩ := card_eq_three.mp hc3
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact not_three_ordered h h1 h3 hS
  · exact not_three_ordered h h2 h3 (by rw [hS]; ext; simp; tauto)
  · omega
  · exact not_three_ordered h h2 h1 (by rw [hS]; ext; simp; tauto)
  · exact not_three_ordered h h1 h2 (by rw [hS]; ext; simp; tauto)
  · omega
  · exact not_three_ordered h h3 h2 (by rw [hS]; ext; simp; tauto)
  · exact not_three_ordered h h3 h1 (by rw [hS]; ext; simp; tauto)

