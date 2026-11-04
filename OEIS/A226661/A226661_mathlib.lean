import OpenProblemsLib

/-
OEIS A226661 (Mathlib). a(n) is the smallest k > 0 for which the 3x+k map
T_k(x) = x/2 (x even), (3x+k)/2 (x odd) has a primitive cycle of positive integers with
exactly n odd elements (primitive: the gcd of the elements is 1). Conjecture: a(n) > 0 for
all n ≥ 1. README result: true (an explicit cycle for every n).

Main theorem `A226661_main`: for every n ≥ 1 there are an odd k > 0 with 3 ∤ k, an x₀ > 0
and a length L > 0 such that, with f i = T_k^[i] x₀ (`Core.T k x` is
`if x % 2 = 0 then x / 2 else (3 * x + k) / 2`): f L = x₀; f 0, …, f (L−1) are pairwise
distinct and positive; exactly n of them are odd; and their gcd is 1. So a(n) > 0.
Proof: the construction of the README with m a prime > 3ⁿ: k = 2^(n+m) − 3ⁿ,
x₀ = 3ⁿ − 2ⁿ; the orbit identities are the core-Lean `step`, `top`, `halve`, `x0_eq` of
`A226661.lean` (copied below in namespace `Core`). Primitivity: a common prime factor q of
x₀ and f 1 divides k and x₀ + k = 2ⁿ(2^m − 1), hence 2^m − 1; then m ∣ q − 1 (ord_q(2) = m
by Mathlib `orderOf_eq_prime`, Fermat by `ZMod.orderOf_dvd_card_sub_one`), so
q > m > 3ⁿ > x₀, impossible.

Outside Lean: nothing. (Generated from certificate/A226661_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-! ### Core-Lean facts, copied verbatim from `A226661.lean` -/
namespace Core
  def T (k x : Nat) : Nat := if x % 2 = 0 then x / 2 else (3 * x + k) / 2

  def y (n m j : Nat) : Nat := 3 ^ j * 2 ^ (n - j) * (2 ^ m - 1)
  def kk (n m : Nat) : Nat := 2 ^ (n + m) - 3 ^ n

  theorem pow3_odd (n : Nat) : 3 ^ n % 2 = 1 := by
    induction n with
    | zero => decide
    | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

  theorem k_odd (n m : Nat) (hm : 1 ≤ m) (h : 3 ^ n < 2 ^ (n + m)) : kk n m % 2 = 1 := by
    have h2 : 2 ^ (n + m) % 2 = 0 := by
      rw [show n + m = (n + m - 1) + 1 by omega, Nat.pow_succ]; exact Nat.mul_mod_left _ 2
    have := pow3_odd n
    unfold kk; omega

  theorem y_ge (n m j : Nat) (hj : j ≤ n) : 2 ^ n * (2 ^ m - 1) ≤ y n m j := by
    unfold y
    apply Nat.mul_le_mul_right
    have h1 : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by decide) j
    have h2 : 2 ^ n = 2 ^ j * 2 ^ (n - j) := by rw [← Nat.pow_add]; congr 1; omega
    rw [h2]
    exact Nat.mul_le_mul_right _ h1

  theorem k_le_y (n m j : Nat) (hj : j ≤ n) : kk n m ≤ y n m j := by
    have := y_ge n m j hj
    have e : 2 ^ n * (2 ^ m - 1) = 2 ^ (n + m) - 2 ^ n := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.pow_add]
    have h3 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by decide) n
    unfold kk; omega

  theorem step (n m j : Nat) (hm : 1 ≤ m) (h : 3 ^ n < 2 ^ (n + m)) (hj : j < n) :
      (y n m j - kk n m) % 2 = 1 ∧ T (kk n m) (y n m j - kk n m) = y n m (j + 1) - kk n m := by
    have hle := k_le_y n m j (by omega)
    have hko := k_odd n m hm h
    have e1 : y n m j = 2 * (3 ^ j * 2 ^ (n - (j + 1)) * (2 ^ m - 1)) := by
      unfold y
      rw [show n - j = (n - (j + 1)) + 1 by omega, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ (n - (j + 1))) 2, ← Nat.mul_assoc, Nat.mul_comm (3 ^ j) 2,
        Nat.mul_assoc 2, Nat.mul_assoc 2, Nat.mul_assoc]
    have e2 : y n m (j + 1) = 3 * (3 ^ j * 2 ^ (n - (j + 1)) * (2 ^ m - 1)) := by
      unfold y
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc 3, Nat.mul_assoc 3, Nat.mul_assoc]
    rw [e1] at hle ⊢
    rw [e2]
    generalize 3 ^ j * 2 ^ (n - (j + 1)) * (2 ^ m - 1) = A at *
    generalize kk n m = k at *
    have hodd : (2 * A - k) % 2 = 1 := by omega
    refine ⟨hodd, ?_⟩
    unfold T
    simp only [show ¬ ((2 * A - k) % 2 = 0) by omega, ↓reduceIte]
    omega

  theorem top (n m : Nat) (h : 3 ^ n < 2 ^ (n + m)) :
      y n m n - kk n m = 2 ^ m * (3 ^ n - 2 ^ n) := by
    unfold y kk
    simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    have h3 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by decide) n
    have e1 : 3 ^ n * (2 ^ m - 1) = 3 ^ n * 2 ^ m - 3 ^ n := by rw [Nat.mul_sub, Nat.mul_one]
    have e2 : 2 ^ m * (3 ^ n - 2 ^ n) = 3 ^ n * 2 ^ m - 2 ^ (n + m) := by
      rw [Nat.mul_sub, Nat.pow_add, Nat.mul_comm (2 ^ m) (3 ^ n), Nat.mul_comm (2 ^ m) (2 ^ n)]
    have h4 : 2 ^ (n + m) ≤ 3 ^ n * 2 ^ m := by
      rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h3
    have h5 : 3 ^ n ≤ 3 ^ n * 2 ^ m := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
    omega

  theorem halve (k i c : Nat) : T k (2 ^ (i + 1) * c) = 2 ^ i * c := by
    unfold T
    have e : 2 ^ (i + 1) * c = 2 * (2 ^ i * c) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]
    rw [e]
    simp only [Nat.mul_mod_right, ↓reduceIte]
    omega

  theorem x0_eq (n m : Nat) (h : 3 ^ n < 2 ^ (n + m)) : y n m 0 - kk n m = 3 ^ n - 2 ^ n := by
    unfold y kk
    simp only [Nat.pow_zero, Nat.one_mul, Nat.sub_zero]
    have h3 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by decide) n
    have e : 2 ^ n * (2 ^ m - 1) = 2 ^ (n + m) - 2 ^ n := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.pow_add]
    omega

  def ms : List Nat := [1, 2, 2, 3, 3, 5, 5, 5, 6, 6, 7, 10, 8, 9, 9, 10, 10, 11, 12, 13,
    13, 13, 14, 17, 15, 17, 16, 17, 17, 19]

  theorem choice_small : (List.range 30).all (fun i =>
      let n := i + 1
      let m := ms.getD i 0
      decide (1 ≤ m) && decide (3 ^ n < 2 ^ (n + m)) && Nat.gcd (3 ^ n - 2 ^ n) (2 ^ m - 1) == 1) = true := by
    decide +kernel
end Core

/-- `p ∣ 2 ^ m - 1` is `(2 : ZMod p) ^ m = 1`. -/
theorem dvd_iff_zmod (p m : ℕ) : p ∣ 2 ^ m - 1 ↔ (2 : ZMod p) ^ m = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow), sub_eq_zero]
  simp

/-- A prime factor q of 2^m − 1 with m prime has m ∣ q − 1. -/
theorem prime_factor_mersenne (m q : ℕ) (hm : m.Prime) (hq : q.Prime) (hd : q ∣ 2 ^ m - 1) :
    m ∣ q - 1 := by
  have := Fact.mk hq
  have := Fact.mk hm
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 : 2 ^ m % 2 = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := hm.two_le; omega⟩
      rw [hk, pow_succ]; simp
    have h3 := Nat.one_le_two_pow (n := m)
    generalize 2 ^ m = x at *
    omega
  have h0 : (2 : ZMod q) ≠ 0 := by
    intro h2
    have : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h2)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this)
  have h1 : (2 : ZMod q) ≠ 1 := by
    intro h
    have : ((2 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    have hq3 : 2 < q := by have := hq.two_le; omega
    rw [Nat.mod_eq_of_lt hq3, Nat.mod_eq_of_lt (by omega)] at this; omega
  have hord : orderOf (2 : ZMod q) = m := orderOf_eq_prime ((dvd_iff_zmod q m).mp hd) h1
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one h0

theorem y_pos (n m j : ℕ) (hm : 1 ≤ m) (hj : j ≤ n) : 0 < Core.y n m j := by
  have := Core.y_ge n m j hj
  have : 1 ≤ 2 ^ m - 1 := by have := Nat.lt_two_pow_self (n := m); have := Nat.one_le_two_pow (n := m); omega
  have : 0 < 2 ^ n * (2 ^ m - 1) := Nat.mul_pos (Nat.two_pow_pos n) (by omega)
  omega

theorem y_succ (n m j : ℕ) (hj : j < n) : Core.y n m (j + 1) * 2 = Core.y n m j * 3 := by
  unfold Core.y
  rw [show n - j = (n - (j + 1)) + 1 by omega, pow_succ, pow_succ]
  ring

theorem y_lt (n m i : ℕ) (hm : 1 ≤ m) : ∀ d, i + d + 1 ≤ n → Core.y n m i < Core.y n m (i + d + 1)
  | 0, h => by
    rw [show i + 0 + 1 = i + 1 by omega]
    have := y_succ n m i (by omega)
    have := y_pos n m i hm (by omega)
    omega
  | d + 1, h => by
    have ih := y_lt n m i hm d (by omega)
    have := y_succ n m (i + d + 1) (by omega)
    have := y_pos n m (i + d + 1) hm (by omega)
    rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega]
    omega

theorem A226661_main (n : ℕ) (hn : 1 ≤ n) :
    ∃ k x₀ L : ℕ, 0 < k ∧ k % 2 = 1 ∧ k % 3 ≠ 0 ∧ 0 < x₀ ∧ 0 < L ∧
      (Core.T k)^[L] x₀ = x₀ ∧
      (∀ i < L, 0 < (Core.T k)^[i] x₀) ∧
      (∀ i < L, ∀ j < L, (Core.T k)^[i] x₀ = (Core.T k)^[j] x₀ → i = j) ∧
      ((Finset.range L).filter (fun i => (Core.T k)^[i] x₀ % 2 = 1)).card = n ∧
      (Finset.range L).gcd (fun i => (Core.T k)^[i] x₀) = 1 := by
  obtain ⟨m, hmgt, hm⟩ := Nat.exists_infinite_primes (3 ^ n + 1)
  have hm1 : 1 ≤ m := hm.one_lt.le
  have h2m : m < 2 ^ m := Nat.lt_two_pow_self
  have h23 : 2 ^ n < 3 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hpow : 3 ^ n < 2 ^ (n + m) := by
    have : 2 ^ m ≤ 2 ^ (n + m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set k := Core.kk n m with hk
  set c := 3 ^ n - 2 ^ n with hc
  have hc0 : 0 < c := by omega
  have hkodd := Core.k_odd n m hm1 hpow
  have h3odd := Core.pow3_odd n
  have h2even : 2 ^ n % 2 = 0 := by
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]; simp
  have hcodd : c % 2 = 1 := by omega
  -- the orbit
  have orb1 : ∀ j, j ≤ n → (Core.T k)^[j] c = Core.y n m j - k := by
    intro j
    induction j with
    | zero => intro _; simp [hc, hk, Core.x0_eq n m hpow]
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact (Core.step n m j hm1 hpow (by omega)).2
  have orb2 : ∀ i, i ≤ m → (Core.T k)^[n + i] c = 2 ^ (m - i) * c := by
    intro i
    induction i with
    | zero => intro _; simp only [Nat.add_zero, Nat.sub_zero]; rw [orb1 n le_rfl, Core.top n m hpow]
    | succ i ih =>
      intro hi
      rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega),
        show m - i = (m - (i + 1)) + 1 by omega, Core.halve]
  have hodd : ∀ j, j < n → (Core.T k)^[j] c % 2 = 1 := by
    intro j hj; rw [orb1 j hj.le]; exact (Core.step n m j hm1 hpow hj).1
  have heven : ∀ i, n ≤ i → i < n + m → (Core.T k)^[i] c % 2 = 0 := by
    intro i h1 h2
    obtain ⟨t, rfl⟩ : ∃ t, i = n + t := ⟨i - n, by omega⟩
    rw [orb2 t (by omega), show m - t = (m - t - 1) + 1 by omega, pow_succ]
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hk0 : 0 < k := by omega
  refine ⟨k, c, n + m, hk0, hkodd, ?_, hc0, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · -- 3 ∤ k
    have h3 : 3 ^ n % 3 = 0 := by
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ]; simp
    have h2 : 2 ^ (n + m) % 3 ≠ 0 := by
      intro h
      have : 3 ∣ 2 ^ (n + m) := Nat.dvd_of_mod_eq_zero h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
      omega
    rw [hk]; unfold Core.kk; omega
  · rw [orb2 m le_rfl]; simp
  · intro i hi
    rcases Nat.lt_or_ge i n with h | h
    · have := hodd i h; omega
    · obtain ⟨t, rfl⟩ : ∃ t, i = n + t := ⟨i - n, by omega⟩
      rw [orb2 t (by omega)]
      exact Nat.mul_pos (Nat.two_pow_pos _) hc0
  · intro i hi j hj hij
    rcases Nat.lt_or_ge i n with h1 | h1 <;> rcases Nat.lt_or_ge j n with h2 | h2
    · rw [orb1 i h1.le, orb1 j h2.le] at hij
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := y_lt n m i hm1 (j - i - 1) (by omega)
        rw [show i + (j - i - 1) + 1 = j by omega] at this
        have := Core.k_le_y n m i h1.le
        omega
      · have := y_lt n m j hm1 (i - j - 1) (by omega)
        rw [show j + (i - j - 1) + 1 = i by omega] at this
        have := Core.k_le_y n m j h2.le
        omega
    · have := hodd i h1; have := heven j h2 hj; omega
    · have := heven i h1 hi; have := hodd j h2; omega
    · obtain ⟨s, rfl⟩ : ∃ s, i = n + s := ⟨i - n, by omega⟩
      obtain ⟨t, rfl⟩ : ∃ t, j = n + t := ⟨j - n, by omega⟩
      rw [orb2 s (by omega), orb2 t (by omega)] at hij
      have := Nat.eq_of_mul_eq_mul_right hc0 hij
      have := Nat.pow_right_injective (le_refl 2) this
      omega
  · have : (Finset.range (n + m)).filter (fun i => (Core.T k)^[i] c % 2 = 1) = Finset.range n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        by_contra h3
        have := heven i (by omega) h1
        omega
      · intro h; exact ⟨by omega, hodd i h⟩
    rw [this, Finset.card_range]
  · -- primitivity: gcd (f 0, f 1) = 1
    have f0 : (Core.T k)^[0] c = c := rfl
    have f1 : (Core.T k)^[1] c = (3 * c + k) / 2 := by
      show Core.T k c = _
      unfold Core.T
      simp only [show ¬ (c % 2 = 0) by omega, ↓reduceIte]
    have hcop : Nat.Coprime c ((3 * c + k) / 2) := by
      apply Nat.coprime_of_dvd
      intro q hq hqc hqf
      have hqk : q ∣ k := by
        have e : k = 2 * ((3 * c + k) / 2) - 3 * c := by omega
        rw [e]
        exact Nat.dvd_sub (Dvd.dvd.mul_left hqf 2) (Dvd.dvd.mul_left hqc 3)
      have hsum : c + k = 2 ^ n * (2 ^ m - 1) := by
        rw [hc, hk]; unfold Core.kk
        rw [Nat.mul_sub, Nat.mul_one, ← pow_add]
        omega
      have hq2 : q ≠ 2 := by rintro rfl; omega
      have hqM : q ∣ 2 ^ m - 1 := by
        have := hsum ▸ Nat.dvd_add hqc hqk
        rcases (Nat.Prime.dvd_mul hq).mp this with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
            (Nat.Prime.dvd_of_dvd_pow hq h)) hq2
        · exact h
      have hmq := prime_factor_mersenne m q hm hq hqM
      have hqle : q ≤ c := Nat.le_of_dvd hc0 hqc
      have hq1 : m ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hmq
      have hc3 : c < 3 ^ n := by have := Nat.two_pow_pos n; rw [hc]; omega
      have hcm : c < m := lt_of_lt_of_le hc3 (by omega)
      omega
    apply Nat.eq_one_of_dvd_one
    have g0 := Finset.gcd_dvd (f := fun i => (Core.T k)^[i] c) (Finset.mem_range.mpr (show 0 < n + m by omega))
    have g1 := Finset.gcd_dvd (f := fun i => (Core.T k)^[i] c) (Finset.mem_range.mpr (show 1 < n + m by omega))
    simp only [f0, f1] at g0 g1
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd g0 g1
