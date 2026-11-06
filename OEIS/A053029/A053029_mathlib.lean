import Mathlib

/-
OEIS A053029 (numbers m with 4 zeros in the Fibonacci numbers mod m) and
OEIS A053031 (numbers m with 1 zero).  Conjectures (entries):
* A053029: m is on the list iff m is odd and all its factors are on the list,
  or m is twice such an odd number.
* A053031: m is on the list iff m is odd and all its factors are on the list,
  or m is 2 or 4 times such an odd number.

Definitions.  `F n = fib n` as an integer.  `IsPer m k`: `F (n + k) ≡ F n
(mod m)` for all n.  `pisano m`: the least `k > 0` with `IsPer m k` (the
Pisano period).  `zeros m`: the number of `n` in `(0, pisano m]` with
`m ∣ F n` (OEIS A001176).  "Factors" is read as prime factors.

Main theorems.
* `A053029_conj`: for m ≥ 3, `zeros m = 4` iff (m odd and every prime factor
  p has `zeros p = 4`) or (m = 2k, k odd, every prime factor of k has
  `zeros p = 4`).  For m = 1, 2 the prime-factor reading of the conjecture
  fails vacuously: `zeros 1 = zeros 2 = 1` (`zeros_one`, `zeros_two`).
* `A053031_conj`: for m ≥ 1, `zeros m = 1` iff (m odd and every prime factor
  p has `zeros p = 1`) or (m = 2k or 4k, k odd, every prime factor of k has
  `zeros p = 1`).

Route.  `alpha m` (rank of apparition), `u m = F (alpha m + 1)`.
`dvd_F_iff`: m ∣ F n iff alpha m ∣ n (via `Nat.fib_gcd`).  `shift`:
F (j N + r) ≡ F (N+1)^j F r when m ∣ F N.  `u_sq`: u^2 ≡ (-1)^alpha
(Cassini).  `zeros_spec`: zeros m is the order of u mod m.
`zeros_eq_four_iff`: zeros m = 4 iff alpha m is odd (m ≥ 3).
`alpha_mod_four`: u ≡ 1 forces alpha ≡ 2 (mod 4) (Lucas numbers,
`L_coprime`).  `zeros_one_of_dvd`: zeros m = 1 passes to divisors d ≥ 3.
`lift_zero`, `lift_good`: lifting from p^j to p^(j+1).  `exists_odd_zero`,
`exists_good`: induction over coprime prime-power factorizations.

Not checked in this file: agreement of `zeros` with the OEIS data terms
(certificate/check.py).
-/

namespace A053029

open Finset

/-- Fibonacci numbers as integers. -/
abbrev F (n : ℕ) : ℤ := (Nat.fib n : ℤ)

theorem F_add_two (n : ℕ) : F (n + 2) = F n + F (n + 1) := by
  simp [F, Nat.fib_add_two]

theorem F_add (a b : ℕ) : F (a + b + 1) = F a * F b + F (a + 1) * F (b + 1) := by
  simp [F, Nat.fib_add]

theorem cassini (n : ℕ) : F (n + 2) * F n - F (n + 1) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp [F]
  | succ n ih =>
    have h1 := F_add_two n
    have h2 := F_add_two (n + 1)
    rw [show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at *
    rw [pow_succ]
    linear_combination (-1 : ℤ) * ih + F (n + 1) * h2 - F (n + 2) * h1

/-- `k` is a period of the Fibonacci numbers mod `m`. -/
def IsPer (m k : ℕ) : Prop := ∀ n, (m : ℤ) ∣ F (n + k) - F n

/-- The Pisano period: the least `k > 0` that is a period (0 if there is none). -/
noncomputable def pisano (m : ℕ) : ℕ := by
  classical exact if h : ∃ k, 0 < k ∧ IsPer m k then Nat.find h else 0

/-- OEIS A001176: the number of zeros among `F_1, ..., F_π` mod `m`, `π` the Pisano period. -/
noncomputable def zeros (m : ℕ) : ℕ := by
  classical exact ((Ioc 0 (pisano m)).filter (fun n => (m : ℤ) ∣ F n)).card

/-- Rank of apparition: the least `n > 0` with `m ∣ F n` (0 if there is none). -/
noncomputable def alpha (m : ℕ) : ℕ := by
  classical exact if h : ∃ n, 0 < n ∧ (m : ℤ) ∣ F n then Nat.find h else 0

theorem exists_zero (m : ℕ) (hm : 0 < m) : ∃ n, 0 < n ∧ (m : ℤ) ∣ F n := by
  have : NeZero m := ⟨by omega⟩
  let T : Equiv.Perm (ZMod m × ZMod m) :=
    { toFun := fun x => (x.2, x.1 + x.2), invFun := fun x => (x.2 - x.1, x.1),
      left_inv := fun x => by ext <;> simp, right_inv := fun x => by ext <;> simp }
  have hT : ∀ k, (T ^ k) (0, 1) = ((Nat.fib k : ZMod m), (Nat.fib (k + 1) : ZMod m)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      simp [T, Nat.fib_add_two]
  refine ⟨orderOf T, orderOf_pos T, ?_⟩
  have h := hT (orderOf T)
  rw [pow_orderOf_eq_one] at h
  have h0 : ((Nat.fib (orderOf T) : ℤ) : ZMod m) = 0 := by
    have := (congrArg Prod.fst h).symm
    simpa using this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0

theorem alpha_spec (m : ℕ) (hm : 0 < m) :
    0 < alpha m ∧ (m : ℤ) ∣ F (alpha m) ∧ ∀ n, 0 < n → n < alpha m → ¬ (m : ℤ) ∣ F n := by
  classical
  have h := exists_zero m hm
  have e : alpha m = Nat.find h := by simp only [alpha]; rw [dite_eq_left h]
  rw [e]
  refine ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun n hn hlt hd => ?_⟩
  exact Nat.find_min h hlt ⟨hn, hd⟩

theorem dvd_F_iff {m : ℕ} (hm : 0 < m) (n : ℕ) : (m : ℤ) ∣ F n ↔ alpha m ∣ n := by
  obtain ⟨ha, hd, hmin⟩ := alpha_spec m hm
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact dvd_zero _
    have hg : (m : ℤ) ∣ F (Nat.gcd n (alpha m)) := by
      have h1 : m ∣ Nat.fib n := Int.natCast_dvd_natCast.1 h
      have h2 : m ∣ Nat.fib (alpha m) := Int.natCast_dvd_natCast.1 hd
      have : m ∣ Nat.fib (Nat.gcd n (alpha m)) := by
        rw [Nat.fib_gcd]; exact Nat.dvd_gcd h1 h2
      exact Int.natCast_dvd_natCast.2 this
    have hgpos : 0 < Nat.gcd n (alpha m) := Nat.gcd_pos_of_pos_left _ hn
    have hgle : Nat.gcd n (alpha m) ≤ alpha m := Nat.le_of_dvd ha (Nat.gcd_dvd_right _ _)
    have heq : Nat.gcd n (alpha m) = alpha m := by
      by_contra hne
      exact hmin _ hgpos (lt_of_le_of_ne hgle hne) hg
    rw [← heq]; exact Nat.gcd_dvd_left _ _
  · intro h
    have : Nat.fib (alpha m) ∣ Nat.fib n := Nat.fib_dvd _ _ h
    exact dvd_trans hd (Int.natCast_dvd_natCast.2 this)

/-- Shift: if `M ∣ F N` then `F (j N + r) ≡ F (N+1)^j F r (mod M)`. -/
theorem shift {M : ℤ} {N : ℕ} (hN : M ∣ F N) :
    ∀ j r, M ∣ F (j * N + r) - F (N + 1) ^ j * F r := by
  have one : ∀ x, M ∣ F (N + x) - F (N + 1) * F x := by
    intro x
    cases x with
    | zero => simpa [F] using hN
    | succ x =>
      have := F_add N x
      rw [show N + (x + 1) = N + x + 1 by ring, this]
      have : F N * F x + F (N + 1) * F (x + 1) - F (N + 1) * F (x + 1) = F N * F x := by ring
      rw [this]; exact dvd_mul_of_dvd_left hN _
  intro j
  induction j with
  | zero => intro r; simp
  | succ j ih =>
    intro r
    have h1 := one (j * N + r)
    have h2 := dvd_mul_of_dvd_right (ih r) (F (N + 1))
    have := dvd_add h1 h2
    rw [show (j + 1) * N + r = N + (j * N + r) by ring]
    convert this using 1
    ring

/-- `u m = F (alpha m + 1)`. -/
noncomputable abbrev u (m : ℕ) : ℤ := F (alpha m + 1)

theorem u_sq {m : ℕ} (hm : 0 < m) : (m : ℤ) ∣ u m ^ 2 - (-1) ^ alpha m := by
  obtain ⟨ha, hd, -⟩ := alpha_spec m hm
  obtain ⟨a, ha'⟩ : ∃ a, alpha m = a + 1 := ⟨alpha m - 1, by omega⟩
  have hc := cassini a
  have h2 := F_add_two a
  simp only [u]
  rw [ha'] at hd ⊢
  rw [show a + 1 + 1 = a + 2 by ring]
  have : F (a + 2) ^ 2 - (-1) ^ (a + 1) = F (a + 1) * (F (a + 2) + F (a + 1)) := by
    linear_combination hc + F (a + 2) * h2
  rw [this]
  exact dvd_mul_of_dvd_left hd _

/-- `N` returns the pair `(F N, F (N+1))` to `(0, 1)` mod `m`. -/
def Good (m N : ℕ) : Prop := (m : ℤ) ∣ F N ∧ (m : ℤ) ∣ F (N + 1) - 1

theorem good_iff {m : ℕ} (hm : 0 < m) (N : ℕ) :
    Good m N ↔ alpha m ∣ N ∧ (m : ℤ) ∣ u m ^ (N / alpha m) - 1 := by
  obtain ⟨ha, hd, -⟩ := alpha_spec m hm
  have hs := shift hd
  constructor
  · rintro ⟨h0, h1⟩
    have hdiv := (dvd_F_iff hm N).1 h0
    refine ⟨hdiv, ?_⟩
    obtain ⟨j, rfl⟩ := hdiv
    rw [Nat.mul_div_cancel_left _ ha]
    have := hs j 1
    have e : F 1 = 1 := by simp [F]
    rw [e, mul_one, mul_comm j (alpha m)] at this
    have := dvd_sub h1 this
    convert this using 1; ring
  · rintro ⟨hdiv, h1⟩
    obtain ⟨j, rfl⟩ := hdiv
    rw [Nat.mul_div_cancel_left _ ha] at h1
    refine ⟨(dvd_F_iff hm _).2 (dvd_mul_right _ _), ?_⟩
    have := hs j 1
    have e : F 1 = 1 := by simp [F]
    rw [e, mul_one, mul_comm j] at this
    have := dvd_add this h1
    convert this using 1; ring

theorem isPer_iff_good {m : ℕ} (k : ℕ) : IsPer m k ↔ Good m k := by
  constructor
  · intro h
    refine ⟨by simpa [F] using h 0, ?_⟩
    have := h 1
    rw [show 1 + k = k + 1 by ring] at this
    simpa [F] using this
  · rintro ⟨h0, h1⟩ n
    have := shift h0 1 n
    rw [one_mul, pow_one] at this
    have := dvd_add this (dvd_mul_of_dvd_left h1 (F n))
    rw [show n + k = k + n by ring]
    convert this using 1; ring

theorem pisano_spec {m : ℕ} (hm : 0 < m) :
    0 < pisano m ∧ Good m (pisano m) ∧ ∀ k, 0 < k → Good m k → pisano m ≤ k := by
  classical
  obtain ⟨ha, -, -⟩ := alpha_spec m hm
  have hex : ∃ k, 0 < k ∧ IsPer m k := by
    refine ⟨alpha m * 4, by positivity, (isPer_iff_good _).2 ((good_iff hm _).2 ⟨dvd_mul_right _ _, ?_⟩)⟩
    rw [Nat.mul_div_cancel_left _ ha]
    have hs := u_sq hm
    have hsq : ((-1 : ℤ) ^ alpha m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    have : u m ^ 4 - 1 = (u m ^ 2 - (-1) ^ alpha m) * (u m ^ 2 + (-1) ^ alpha m) +
        (((-1 : ℤ) ^ alpha m) ^ 2 - 1) := by ring
    rw [this, hsq, sub_self, add_zero]
    exact dvd_mul_of_dvd_left hs _
  have e : pisano m = Nat.find hex := by simp only [pisano]; rw [dite_eq_left hex]
  rw [e]
  refine ⟨(Nat.find_spec hex).1, (isPer_iff_good _).1 (Nat.find_spec hex).2, fun k hk hg => ?_⟩
  exact Nat.find_min' hex ⟨hk, (isPer_iff_good _).2 hg⟩

theorem zeros_eq {m : ℕ} (hm : 0 < m) : zeros m = pisano m / alpha m := by
  classical
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  unfold zeros
  congr 1
  ext n
  simp only [Finset.mem_filter]
  rw [dvd_F_iff hm]

/-- `zeros m` is the least `J > 0` with `u m ^ J ≡ 1 (mod m)`. -/
theorem zeros_spec {m : ℕ} (hm : 0 < m) :
    0 < zeros m ∧ (m : ℤ) ∣ u m ^ zeros m - 1 ∧
      ∀ i, 0 < i → (m : ℤ) ∣ u m ^ i - 1 → zeros m ≤ i := by
  obtain ⟨ha, -, -⟩ := alpha_spec m hm
  obtain ⟨hp, hg, hmin⟩ := pisano_spec hm
  obtain ⟨hdiv, hu⟩ := (good_iff hm _).1 hg
  rw [zeros_eq hm]
  obtain ⟨j, hj⟩ := hdiv
  have hjq : pisano m / alpha m = j := by rw [hj, Nat.mul_div_cancel_left _ ha]
  rw [hjq] at hu ⊢
  refine ⟨Nat.pos_of_ne_zero (by rintro rfl; rw [hj] at hp; simp at hp), hu, fun i hi hdi => ?_⟩
  have := hmin (alpha m * i) (by positivity)
    ((good_iff hm _).2 ⟨dvd_mul_right _ _, by rwa [Nat.mul_div_cancel_left _ ha]⟩)
  rw [hj] at this
  exact Nat.le_of_mul_le_mul_left this ha

theorem zeros_eq_one_iff {m : ℕ} (hm : 0 < m) : zeros m = 1 ↔ (m : ℤ) ∣ u m - 1 := by
  obtain ⟨hp, hu, hmin⟩ := zeros_spec hm
  constructor
  · intro h; rw [h, pow_one] at hu; exact hu
  · intro h
    have := hmin 1 one_pos (by rwa [pow_one])
    omega

/-! ## Helpers -/

theorem neg_one_pow_cases (n : ℕ) :
    ((-1 : ℤ) ^ n = 1 ∧ Even n) ∨ ((-1 : ℤ) ^ n = -1 ∧ Odd n) := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl ⟨h.neg_one_pow, h⟩
  · exact Or.inr ⟨h.neg_one_pow, h⟩

theorem le_two_of_dvd_two {m : ℕ} (h : (m : ℤ) ∣ 2) : m ≤ 2 := by
  have : m ∣ 2 := by exact_mod_cast h
  exact Nat.le_of_dvd (by norm_num) this

/-- `x ^ j ≡ x ^ (j % d)` when `x ^ d ≡ 1`. -/
theorem pow_mod_period {M x : ℤ} {d : ℕ} (h : M ∣ x ^ d - 1) (j : ℕ) :
    M ∣ x ^ j - x ^ (j % d) := by
  have hx : x ^ j = (x ^ d) ^ (j / d) * x ^ (j % d) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have e : x ^ j - x ^ (j % d) = x ^ (j % d) * ((x ^ d) ^ (j / d) - 1) := by
    rw [hx]; ring
  rw [e]
  have h2 : x ^ d - 1 ∣ (x ^ d) ^ (j / d) - 1 := by
    simpa using sub_dvd_pow_sub_pow (x ^ d) 1 (j / d)
  exact dvd_mul_of_dvd_right (dvd_trans h h2) _

/-- If `x ^ 2 ≡ -1` and `x ^ r ≡ 1` with `0 < r < 4`, then `M ∣ 2`. -/
theorem two_of_pow {M x : ℤ} (h : M ∣ x ^ 2 - -1) {r : ℕ} (hr1 : 0 < r) (hr : r < 4)
    (hd : M ∣ x ^ r - 1) : M ∣ 2 := by
  interval_cases r
  · have e : (2 : ℤ) = (x ^ 2 - -1) - (x + 1) * (x ^ 1 - 1) := by ring
    rw [e]; exact dvd_sub h (dvd_mul_of_dvd_left hd _ |>.trans (by rw [mul_comm]))
  · have e : (2 : ℤ) = (x ^ 2 - -1) - (x ^ 2 - 1) := by ring
    rw [e]; exact dvd_sub h hd
  · have h1 : M ∣ x + 1 := by
      have e : x + 1 = x * (x ^ 2 - -1) - (x ^ 3 - 1) := by ring
      rw [e]; exact dvd_sub (dvd_mul_of_dvd_right h _) hd
    have e : (2 : ℤ) = (x ^ 2 - -1) - (x - 1) * (x + 1) := by ring
    rw [e]; exact dvd_sub h (dvd_mul_of_dvd_right h1 _)

theorem alpha_dvd {d m : ℕ} (hm : 0 < m) (hd : d ∣ m) : alpha d ∣ alpha m := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hm
  obtain ⟨-, h, -⟩ := alpha_spec m hm
  exact (dvd_F_iff hd0 _).1 (dvd_trans (Int.natCast_dvd_natCast.2 hd) h)

theorem u_div {d m : ℕ} (hm : 0 < m) (hd : d ∣ m) :
    (d : ℤ) ∣ u m - u d ^ (alpha m / alpha d) := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hm
  obtain ⟨ha, h, -⟩ := alpha_spec d hd0
  obtain ⟨j, hj⟩ := alpha_dvd hm hd
  have hs := shift h j 1
  have e : F 1 = 1 := by simp [F]
  rw [e, mul_one, mul_comm j, ← hj] at hs
  rw [show alpha m / alpha d = j by rw [hj, Nat.mul_div_cancel_left _ ha]]
  exact hs

theorem alpha_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : (m : ℤ) ∣ F n)
    (hmin : ∀ i, 0 < i → i < n → ¬ (m : ℤ) ∣ F i) : alpha m = n := by
  obtain ⟨ha, hd, -⟩ := alpha_spec m hm
  have h1 : alpha m ∣ n := (dvd_F_iff hm n).1 h
  have h2 : alpha m ≤ n := Nat.le_of_dvd hn h1
  by_contra hne
  exact hmin _ ha (lt_of_le_of_ne h2 hne) hd

theorem alpha_two : alpha 2 = 3 :=
  alpha_eq (by norm_num) (by norm_num) (by norm_num [F]) (by
    intro i h1 h2; interval_cases i <;> norm_num [F])

theorem alpha_four : alpha 4 = 6 :=
  alpha_eq (by norm_num) (by norm_num) (by norm_num [F]) (by
    intro i h1 h2; interval_cases i <;> norm_num [F])

theorem alpha_eight : alpha 8 = 6 :=
  alpha_eq (by norm_num) (by norm_num) (by norm_num [F]) (by
    intro i h1 h2; interval_cases i <;> norm_num [F])

theorem zeros_one : zeros 1 = 1 := (zeros_eq_one_iff (by norm_num)).2 (by simp)

theorem zeros_two : zeros 2 = 1 := by
  rw [zeros_eq_one_iff (by norm_num), u, alpha_two]
  norm_num [F]

theorem zeros_eight : zeros 8 ≠ 1 := by
  rw [Ne, zeros_eq_one_iff (by norm_num), u, alpha_eight]
  norm_num [F]

/-! ## Four zeros -/

theorem zeros_eq_four_iff {m : ℕ} (hm : 3 ≤ m) : zeros m = 4 ↔ Odd (alpha m) := by
  have hm0 : 0 < m := by omega
  obtain ⟨hp, hu, hmin⟩ := zeros_spec hm0
  have hsq := u_sq hm0
  have no2 : ¬ (m : ℤ) ∣ 2 := fun h => by have := le_two_of_dvd_two h; omega
  constructor
  · intro h4
    rcases neg_one_pow_cases (alpha m) with ⟨he, -⟩ | ⟨-, hodd⟩
    · rw [he] at hsq
      have := hmin 2 (by norm_num) hsq
      omega
    · exact hodd
  · intro hodd
    rw [hodd.neg_one_pow] at hsq
    have h4 : (m : ℤ) ∣ u m ^ 4 - 1 := by
      have e : u m ^ 4 - 1 = (u m ^ 2 - -1) * (u m ^ 2 - 1) := by ring
      rw [e]; exact dvd_mul_of_dvd_left hsq _
    have hle := hmin 4 (by norm_num) h4
    by_contra hne
    exact no2 (two_of_pow hsq hp (by omega) hu)

/-! ## Lucas numbers and the residue of the rank -/

/-- Lucas numbers. -/
abbrev L (n : ℕ) : ℤ := 2 * F (n + 1) - F n

theorem L_coprime (n : ℕ) : IsCoprime (L n) (L (n + 1)) := by
  induction n with
  | zero =>
    have e : L (0 + 1) = 1 := by norm_num [L, F]
    rw [e]; exact isCoprime_one_right
  | succ n ih =>
    obtain ⟨x, y, h⟩ := ih
    refine ⟨y - x, x, ?_⟩
    have h2 : F (n + 2) = F n + F (n + 1) := F_add_two n
    have h3 : F (n + 3) = F (n + 1) + F (n + 2) := F_add_two (n + 1)
    show (y - x) * (2 * F (n + 2) - F (n + 1)) + x * (2 * F (n + 3) - F (n + 2)) = 1
    have h' : x * (2 * F (n + 1) - F n) + y * (2 * F (n + 2) - F (n + 1)) = 1 := h
    linear_combination h' + x * (2 * h3 - h2)

theorem F_two_mul (h : ℕ) : F (2 * h) = F h * L h := by
  rcases h with _ | h
  · simp [F, L]
  · have e1 : F (2 * (h + 1)) = F h * F (h + 1) + F (h + 1) * F (h + 2) := by
      rw [show 2 * (h + 1) = h + (h + 1) + 1 by ring]; exact F_add h (h + 1)
    have e2 : F (h + 2) = F h + F (h + 1) := F_add_two h
    rw [e1]
    show _ = F (h + 1) * (2 * F (h + 2) - F (h + 1))
    linear_combination (-F (h + 1)) * e2

theorem F_two_mul_add_one (h : ℕ) : F (2 * h + 1) - (-1) ^ h = F h * L (h + 1) := by
  have e1 : F (2 * h + 1) = F h * F h + F (h + 1) * F (h + 1) := by
    rw [show 2 * h + 1 = h + h + 1 by ring]; exact F_add h h
  have e2 : F (h + 2) = F h + F (h + 1) := F_add_two h
  have c := cassini h
  rw [e1]
  show _ = F h * (2 * F (h + 2) - F (h + 1))
  linear_combination (-1 : ℤ) * c + (-F h) * e2

theorem alpha_mod_four {m : ℕ} (hm : 3 ≤ m) (h1 : (m : ℤ) ∣ u m - 1) : alpha m % 4 = 2 := by
  have hm0 : 0 < m := by omega
  obtain ⟨ha, hd, hmin⟩ := alpha_spec m hm0
  have hsq := u_sq hm0
  have no2 : ¬ (m : ℤ) ∣ 2 := fun h => by have := le_two_of_dvd_two h; omega
  have hev : Even (alpha m) := by
    rcases neg_one_pow_cases (alpha m) with ⟨-, h⟩ | ⟨ho, -⟩
    · exact h
    · exfalso; apply no2; rw [ho] at hsq
      have e : (2 : ℤ) = (u m ^ 2 - -1) - (u m + 1) * (u m - 1) := by ring
      rw [e]; exact dvd_sub hsq (dvd_mul_of_dvd_left h1 _ |>.trans (by rw [mul_comm]))
  obtain ⟨h, hh⟩ := hev
  have hpos : 0 < h := by omega
  rcases Nat.even_or_odd h with he | ho
  · exfalso
    have hA : (m : ℤ) ∣ F h * L h := by
      rw [← F_two_mul, show 2 * h = alpha m by omega]; exact hd
    have hB : (m : ℤ) ∣ F h * L (h + 1) := by
      rw [← F_two_mul_add_one, he.neg_one_pow, show 2 * h + 1 = alpha m + 1 by omega]; exact h1
    obtain ⟨x, y, hxy⟩ := L_coprime h
    have hFh : (m : ℤ) ∣ F h := by
      have e : F h = x * (F h * L h) + y * (F h * L (h + 1)) := by
        linear_combination (-F h) * hxy
      rw [e]; exact dvd_add (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hB _)
    exact hmin h hpos (by omega) hFh
  · obtain ⟨k, hk⟩ := ho; omega

/-! ## Lifting to prime powers -/

theorem lift_aux (q a : ℤ) (n : ℕ) (hN : F (n + 1) = q * a) :
    ∀ k : ℕ, ∃ s t : ℤ,
      F ((k + 1) * (n + 1)) = ((k : ℤ) + 1) * q * a * F (n + 2) ^ k + q ^ 2 * s ∧
      F ((k + 1) * (n + 1) + 1) = F (n + 2) ^ (k + 1) + q ^ 2 * t := by
  have hFn : F n = F (n + 2) - q * a := by
    have g := F_add_two n
    linear_combination -g - hN
  intro k
  induction k with
  | zero =>
    refine ⟨0, 0, ?_, ?_⟩
    · simp [hN]
    · simp
  | succ k ih =>
    obtain ⟨s, t, hs, ht⟩ := ih
    have f1 := F_add ((k + 1) * (n + 1)) n
    have f2 := F_add ((k + 1) * (n + 1)) (n + 1)
    rw [show (k + 1 + 1) * (n + 1) = (k + 1) * (n + 1) + n + 1 by ring, f1,
      show (k + 1) * (n + 1) + n + 1 + 1 = (k + 1) * (n + 1) + (n + 1) + 1 by ring, f2]
    rw [hs, ht, hN, hFn, show n + 1 + 1 = n + 2 by ring]
    refine ⟨-((k : ℤ) + 1) * a ^ 2 * F (n + 2) ^ k + s * F (n + 2) - q * a * s + q * a * t,
      ((k : ℤ) + 1) * a ^ 2 * F (n + 2) ^ k + q * a * s + t * F (n + 2), ?_, ?_⟩
    · push_cast; ring
    · ring

theorem lift_zero {p j N : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (hN0 : 0 < N)
    (h : (p : ℤ) ^ j ∣ F N) : (p : ℤ) ^ (j + 1) ∣ F (p * N) := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨s, t, hs, -⟩ := lift_aux ((p : ℤ) ^ (j' + 1)) a n ha k
  have hk' : ((k : ℤ) + 1) = p := by rw [hk]; push_cast; ring
  rw [show p * (n + 1) = (k + 1) * (n + 1) by rw [hk], hs, hk']
  exact ⟨a * F (n + 2) ^ k + (p : ℤ) ^ j' * s, by ring⟩

theorem pq_dvd_pow_sub_one {p : ℕ} {q c : ℤ} (hq : q ∣ c - 1) (hpq : (p : ℤ) ∣ q) :
    (p : ℤ) * q ∣ c ^ p - 1 := by
  have hS : (p : ℤ) ∣ ∑ i ∈ range p, c ^ i := by
    have e : ∑ i ∈ range p, c ^ i = ∑ i ∈ range p, (c ^ i - 1) + p := by
      rw [Finset.sum_sub_distrib]; simp
    rw [e]
    refine dvd_add (Finset.dvd_sum fun i _ => ?_) (dvd_refl _)
    exact dvd_trans hpq (dvd_trans hq (by simpa using sub_dvd_pow_sub_pow c 1 i))
  rw [← mul_geom_sum, mul_comm (p : ℤ) q]
  exact mul_dvd_mul hq hS

theorem lift_good {p j N : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (hN0 : 0 < N)
    (h : Good (p ^ j) N) : Good (p ^ (j + 1)) (p * N) := by
  obtain ⟨h0, h1⟩ := h
  push_cast at h0 h1 ⊢
  obtain ⟨a, ha⟩ := h0
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨s, t, hs, ht⟩ := lift_aux ((p : ℤ) ^ (j' + 1)) a n ha k
  have hk' : ((k : ℤ) + 1) = p := by rw [hk]; push_cast; ring
  have e : p * (n + 1) = (k + 1) * (n + 1) := by rw [hk]
  refine ⟨?_, ?_⟩
  · rw [e, hs, hk']
    exact ⟨a * F (n + 2) ^ k + (p : ℤ) ^ j' * s, by push_cast; ring⟩
  · rw [e, ht, ← hk, show n + 1 + 1 = n + 2 by ring] 
    have hc : (p : ℤ) * (p : ℤ) ^ (j' + 1) ∣ F (n + 2) ^ p - 1 :=
      pq_dvd_pow_sub_one (by rw [show n + 1 + 1 = n + 2 by ring] at h1; exact h1)
        (dvd_pow_self _ (by omega))
    have e2 : F (n + 2) ^ p + ((p : ℤ) ^ (j' + 1)) ^ 2 * t - 1 =
        (F (n + 2) ^ p - 1) + (p : ℤ) ^ (j' + 1 + 1) * ((p : ℤ) ^ j' * t) := by ring
    rw [e2]
    refine dvd_add ?_ (dvd_mul_right _ _)
    rw [pow_succ']; exact hc

theorem good_mul {m N : ℕ} (h : Good m N) (k : ℕ) : Good m (k * N) := by
  obtain ⟨h0, h1⟩ := h
  have hs0 := shift h0 k 0
  have hs1 := shift h0 k 1
  have e0 : F 0 = 0 := by simp [F]
  have e1 : F 1 = 1 := by simp [F]
  rw [e0, mul_zero, sub_zero, add_zero] at hs0
  rw [e1, mul_one] at hs1
  refine ⟨hs0, ?_⟩
  have hc : (m : ℤ) ∣ F (N + 1) ^ k - 1 :=
    dvd_trans h1 (by simpa using sub_dvd_pow_sub_pow (F (N + 1)) 1 k)
  have := dvd_add hs1 hc
  convert this using 1; ring

theorem good_merge {a b N : ℕ} (hab : Nat.Coprime a b) (ga : Good a N) (gb : Good b N) :
    Good (a * b) N := by
  have hc := Nat.Coprime.isCoprime hab
  refine ⟨?_, ?_⟩ <;> rw [Nat.cast_mul]
  · exact hc.mul_dvd ga.1 gb.1
  · exact hc.mul_dvd ga.2 gb.2

/-! ## Existence of suitable indices -/

theorem exists_odd_zero : ∀ m : ℕ, ¬ 4 ∣ m →
    (∀ p, p.Prime → p ∣ m → p ≠ 2 → Odd (alpha p)) → ∃ N, Odd N ∧ (m : ℤ) ∣ F N := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro h4 hodd
    by_cases hp2 : p = 2
    · subst hp2
      have hn1 : n = 1 := by
        by_contra hne
        exact h4 (dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 (by omega)))
      subst hn1
      exact ⟨3, by decide, by norm_num [F]⟩
    · have ha := hodd p hp (dvd_pow_self p (by omega)) hp2
      obtain ⟨ha0, had, -⟩ := alpha_spec p hp.pos
      have key : ∀ j, (p : ℤ) ^ (j + 1) ∣ F (p ^ j * alpha p) := by
        intro j
        induction j with
        | zero => simpa using had
        | succ j ih =>
          have := lift_zero hp (by omega) (Nat.mul_pos (pow_pos hp.pos _) ha0) ih
          rw [show p ^ (j + 1) * alpha p = p * (p ^ j * alpha p) by ring]
          exact this
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      refine ⟨p ^ n' * alpha p, ?_, by push_cast; exact key n'⟩
      exact ((hp.odd_of_ne_two hp2).pow).mul ha
  | zero => intro h4; exact absurd (dvd_zero 4) h4
  | one => intro _ _; exact ⟨1, odd_one, by simp⟩
  | coprime a b ha hb hab iha ihb =>
    intro h4 hodd
    obtain ⟨Na, hNa, hda⟩ := iha (fun h => h4 (dvd_mul_of_dvd_left h b))
      (fun p hp hpa => hodd p hp (dvd_mul_of_dvd_left hpa b))
    obtain ⟨Nb, hNb, hdb⟩ := ihb (fun h => h4 (dvd_mul_of_dvd_right h a))
      (fun p hp hpb => hodd p hp (dvd_mul_of_dvd_right hpb a))
    refine ⟨Na * Nb, hNa.mul hNb, ?_⟩
    have h1 : F Na ∣ F (Na * Nb) :=
      Int.natCast_dvd_natCast.2 (Nat.fib_dvd _ _ (dvd_mul_right _ _))
    have h2 : F Nb ∣ F (Na * Nb) :=
      Int.natCast_dvd_natCast.2 (Nat.fib_dvd _ _ (dvd_mul_left _ _))
    rw [Nat.cast_mul]
    exact (Nat.Coprime.isCoprime hab).mul_dvd (dvd_trans hda h1) (dvd_trans hdb h2)

theorem exists_good : ∀ m : ℕ, ¬ 8 ∣ m →
    (∀ p, p.Prime → p ∣ m → p ≠ 2 → zeros p = 1) → ∃ N, N % 4 = 2 ∧ Good m N := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro h8 h1
    by_cases hp2 : p = 2
    · subst hp2
      have hn2 : n ≤ 2 := by
        by_contra hne
        exact h8 (dvd_trans (by norm_num : 8 ∣ 2 ^ 3) (pow_dvd_pow 2 (by omega)))
      refine ⟨6, rfl, ?_⟩
      have h4 : ((2 ^ n : ℕ) : ℤ) ∣ 4 := by
        have : 2 ^ n ∣ 4 := dvd_trans (pow_dvd_pow 2 hn2) (by norm_num)
        exact_mod_cast this
      exact ⟨dvd_trans h4 (by norm_num [F]), dvd_trans h4 (by norm_num [F])⟩
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hz := h1 p hp (dvd_pow_self p (by omega)) hp2
      have hu := (zeros_eq_one_iff hp.pos).1 hz
      have hmod := alpha_mod_four hp3 hu
      obtain ⟨ha0, had, -⟩ := alpha_spec p hp.pos
      have key : ∀ j, Good (p ^ (j + 1)) (p ^ j * alpha p) := by
        intro j
        induction j with
        | zero => simpa [Good] using And.intro had hu
        | succ j ih =>
          have := lift_good hp (by omega) (Nat.mul_pos (pow_pos hp.pos _) ha0) ih
          rw [show p ^ (j + 1) * alpha p = p * (p ^ j * alpha p) by ring]
          exact this
      have hmodj : ∀ j, (p ^ j * alpha p) % 4 = 2 := by
        intro j
        have hpj : p ^ j % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
        rw [Nat.mul_mod, hmod]
        have : p ^ j % 4 = 1 ∨ p ^ j % 4 = 3 := by omega
        rcases this with h | h <;> rw [h]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact ⟨p ^ n' * alpha p, hmodj n', key n'⟩
  | zero => intro h8; exact absurd (dvd_zero 8) h8
  | one => intro _ _; exact ⟨6, rfl, by simp [Good]⟩
  | coprime a b ha hb hab iha ihb =>
    intro h8 h1
    obtain ⟨Na, hNa, ga⟩ := iha (fun h => h8 (dvd_mul_of_dvd_left h b))
      (fun p hp hpa => h1 p hp (dvd_mul_of_dvd_left hpa b))
    obtain ⟨Nb, hNb, gb⟩ := ihb (fun h => h8 (dvd_mul_of_dvd_right h a))
      (fun p hp hpb => h1 p hp (dvd_mul_of_dvd_right hpb a))
    obtain ⟨A, rfl, hA⟩ : ∃ A, Na = 2 * A ∧ A % 2 = 1 := ⟨Na / 2, by omega, by omega⟩
    obtain ⟨B, rfl, hB⟩ : ∃ B, Nb = 2 * B ∧ B % 2 = 1 := ⟨Nb / 2, by omega, by omega⟩
    have hAB : (A * B) % 2 = 1 := by rw [Nat.mul_mod, hA, hB]
    refine ⟨2 * (A * B), by omega, ?_⟩
    have g1 := good_mul ga B
    have g2 := good_mul gb A
    rw [show B * (2 * A) = 2 * (A * B) by ring] at g1
    rw [show A * (2 * B) = 2 * (A * B) by ring] at g2
    exact good_merge hab g1 g2

/-! ## One zero -/

theorem zeros_one_of_good {m N : ℕ} (hm : 3 ≤ m) (hN : N % 4 = 2) (hg : Good m N) :
    zeros m = 1 := by
  have hm0 : 0 < m := by omega
  obtain ⟨ha, -, -⟩ := alpha_spec m hm0
  obtain ⟨hdiv, hu⟩ := (good_iff hm0 N).1 hg
  obtain ⟨j, rfl⟩ := hdiv
  rw [Nat.mul_div_cancel_left _ ha] at hu
  have hsq := u_sq hm0
  have no2 : ¬ (m : ℤ) ∣ 2 := fun h => by have := le_two_of_dvd_two h; omega
  rcases neg_one_pow_cases (alpha m) with ⟨he, hev⟩ | ⟨ho, hodd⟩
  · rw [he] at hsq
    have hr := pow_mod_period hsq j
    have hj : j % 2 = 1 := by
      by_contra hne
      obtain ⟨s, hs⟩ := hev
      have hj0 : j % 2 = 0 := by omega
      obtain ⟨t, ht⟩ : ∃ t, j = 2 * t := ⟨j / 2, by omega⟩
      rw [hs, ht] at hN
      have : (s + s) * (2 * t) = 4 * (s * t) := by ring
      rw [this] at hN
      omega
    rw [hj, pow_one] at hr
    rw [zeros_eq_one_iff hm0]
    have := dvd_sub hu hr
    convert this using 1; ring
  · rw [ho] at hsq
    have h4 : (m : ℤ) ∣ u m ^ 4 - 1 := by
      have e : u m ^ 4 - 1 = (u m ^ 2 - -1) * (u m ^ 2 - 1) := by ring
      rw [e]; exact dvd_mul_of_dvd_left hsq _
    have hr := pow_mod_period h4 j
    have hr' : (m : ℤ) ∣ u m ^ (j % 4) - 1 := by
      have := dvd_sub hu hr
      convert this using 1; ring
    have hj0 : j % 4 ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ : ∃ t, j = 4 * t := ⟨j / 4, by omega⟩
      rw [ht, show alpha m * (4 * t) = 4 * (alpha m * t) by ring] at hN
      omega
    exact absurd (two_of_pow hsq (by omega) (Nat.mod_lt _ (by norm_num)) hr') no2

theorem zeros_one_of_dvd {m d : ℕ} (hm : 3 ≤ m) (hz : zeros m = 1) (hd : d ∣ m) (hd3 : 3 ≤ d) :
    zeros d = 1 := by
  have hm0 : 0 < m := by omega
  have hd0 : 0 < d := by omega
  have hu := (zeros_eq_one_iff hm0).1 hz
  have hmod := alpha_mod_four hm hu
  obtain ⟨had0, -, -⟩ := alpha_spec d hd0
  obtain ⟨j, hj⟩ := alpha_dvd hm0 hd
  have hud := u_div hm0 hd
  rw [hj, Nat.mul_div_cancel_left _ had0] at hud
  have hdu : (d : ℤ) ∣ u d ^ j - 1 := by
    have := dvd_sub (dvd_trans (Int.natCast_dvd_natCast.2 hd) hu) hud
    convert this using 1; ring
  have hsq := u_sq hd0
  have no2 : ¬ (d : ℤ) ∣ 2 := fun h => by have := le_two_of_dvd_two h; omega
  rw [hj, Nat.mul_mod] at hmod
  rcases neg_one_pow_cases (alpha d) with ⟨he, hev⟩ | ⟨ho, hodd⟩
  · rw [he] at hsq
    have hr := pow_mod_period hsq j
    have hj1 : j % 2 = 1 := by
      obtain ⟨s, hs⟩ := hev
      have h0 : alpha d % 4 = 0 ∨ alpha d % 4 = 2 := by omega
      have hj4 : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rcases h0 with h0 | h0 <;> rw [h0] at hmod <;> omega
    rw [hj1, pow_one] at hr
    rw [zeros_eq_one_iff hd0]
    have := dvd_sub hdu hr
    convert this using 1; ring
  · rw [ho] at hsq
    have h4 : (d : ℤ) ∣ u d ^ 4 - 1 := by
      have e : u d ^ 4 - 1 = (u d ^ 2 - -1) * (u d ^ 2 - 1) := by ring
      rw [e]; exact dvd_mul_of_dvd_left hsq _
    have hj2 : j % 4 = 2 := by
      have h0 : alpha d % 4 = 1 ∨ alpha d % 4 = 3 := by
        have := Nat.odd_iff.1 hodd; omega
      have hj4 : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rcases h0 with h0 | h0 <;> rw [h0] at hmod <;> omega
    have hr := pow_mod_period h4 j
    rw [hj2] at hr
    have hr' : (d : ℤ) ∣ u d ^ 2 - 1 := by
      have := dvd_sub hdu hr
      convert this using 1; ring
    exact absurd (two_of_pow hsq (by norm_num) (by norm_num) hr') no2

/-! ## The two conjectures -/

/-- **A053029 conjecture** (four zeros), for `m ≥ 3`, with "factors" read as prime factors. -/
theorem A053029_conj (m : ℕ) (hm : 3 ≤ m) :
    zeros m = 4 ↔ (Odd m ∧ ∀ p, p.Prime → p ∣ m → zeros p = 4) ∨
      (∃ k, m = 2 * k ∧ Odd k ∧ ∀ p, p.Prime → p ∣ k → zeros p = 4) := by
  have hm0 : 0 < m := by omega
  rw [zeros_eq_four_iff hm]
  have prime_iff : ∀ p, p.Prime → p ≠ 2 → (zeros p = 4 ↔ Odd (alpha p)) := fun p hp hp2 =>
    zeros_eq_four_iff (by have := hp.two_le; omega)
  have two_of : ∀ p, p.Prime → p ∣ 2 → p = 2 := fun p hp h =>
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
  constructor
  · intro hodd
    have hdiv : ∀ p, p.Prime → p ∣ m → p ≠ 2 → zeros p = 4 := fun p hp hpm hp2 =>
      (prime_iff p hp hp2).2 (Odd.of_dvd_nat hodd (alpha_dvd hm0 hpm))
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | hmo
    · right
      have hko : Odd k := by
        rcases Nat.even_or_odd k with ⟨k', hk'⟩ | hko
        · exfalso
          have h4 : 4 ∣ m := ⟨k', by omega⟩
          have h6 := alpha_dvd hm0 h4
          rw [alpha_four] at h6
          obtain ⟨c, hc⟩ := h6
          have := Nat.odd_iff.1 hodd
          omega
        · exact hko
      refine ⟨k, by omega, hko, fun p hp hpk => ?_⟩
      have hp2 : p ≠ 2 := by
        rintro rfl
        obtain ⟨c, hc⟩ := hpk
        have := Nat.odd_iff.1 hko
        omega
      exact hdiv p hp (dvd_trans hpk ⟨2, by omega⟩) hp2
    · left
      refine ⟨hmo, fun p hp hpm => hdiv p hp hpm ?_⟩
      rintro rfl
      obtain ⟨c, hc⟩ := hpm
      have := Nat.odd_iff.1 hmo
      omega
  · intro h
    have cond : ¬ 4 ∣ m ∧ ∀ p, p.Prime → p ∣ m → p ≠ 2 → Odd (alpha p) := by
      rcases h with ⟨hmo, hp⟩ | ⟨k, rfl, hko, hp⟩
      · refine ⟨fun h4 => ?_, fun p hpp hpm hp2 => (prime_iff p hpp hp2).1 (hp p hpp hpm)⟩
        obtain ⟨c, hc⟩ := h4
        have := Nat.odd_iff.1 hmo
        omega
      · refine ⟨fun h4 => ?_, fun p hpp hpm hp2 => (prime_iff p hpp hp2).1 (hp p hpp ?_)⟩
        · obtain ⟨c, hc⟩ := h4
          have := Nat.odd_iff.1 hko
          omega
        · rcases (Nat.Prime.dvd_mul hpp).1 hpm with h2 | hk
          · exact absurd (two_of p hpp h2) hp2
          · exact hk
    obtain ⟨N, hN, hd⟩ := exists_odd_zero m cond.1 cond.2
    exact Odd.of_dvd_nat hN ((dvd_F_iff hm0 N).1 hd)

/-- **A053031 conjecture** (one zero), for every `m ≥ 1`, with "factors" read as prime factors. -/
theorem A053031_conj (m : ℕ) (hm : 1 ≤ m) :
    zeros m = 1 ↔ (Odd m ∧ ∀ p, p.Prime → p ∣ m → zeros p = 1) ∨
      (∃ k, (m = 2 * k ∨ m = 4 * k) ∧ Odd k ∧ ∀ p, p.Prime → p ∣ k → zeros p = 1) := by
  have two_of : ∀ p, p.Prime → p ∣ 2 → p = 2 := fun p hp h =>
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
  constructor
  · intro hz
    by_cases hm3 : 3 ≤ m
    · have hdiv : ∀ p, p.Prime → p ∣ m → p ≠ 2 → zeros p = 1 := fun p hp hpm hp2 =>
        zeros_one_of_dvd hm3 hz hpm (by have := hp.two_le; omega)
      have h8 : ¬ 8 ∣ m := fun h8 => zeros_eight (zeros_one_of_dvd hm3 hz h8 (by norm_num))
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | hmo
      · right
        have hdk : ∀ k', m = 2 * k' ∨ m = 4 * k' → Odd k' →
            ∀ p, p.Prime → p ∣ k' → zeros p = 1 := by
          intro k' hk' hko p hp hpk
          have hp2 : p ≠ 2 := by
            rintro rfl
            obtain ⟨c, hc⟩ := hpk
            have := Nat.odd_iff.1 hko
            omega
          refine hdiv p hp (dvd_trans hpk ?_) hp2
          rcases hk' with h | h
          · exact ⟨2, by omega⟩
          · exact ⟨4, by omega⟩
        rcases Nat.even_or_odd k with ⟨k', hk'⟩ | hko
        · have hko' : Odd k' := by
            rcases Nat.even_or_odd k' with ⟨c, hc⟩ | h
            · exact absurd ⟨c, by omega⟩ h8
            · exact h
          exact ⟨k', Or.inr (by omega), hko', hdk k' (Or.inr (by omega)) hko'⟩
        · exact ⟨k, Or.inl (by omega), hko, hdk k (Or.inl (by omega)) hko⟩
      · left
        refine ⟨hmo, fun p hp hpm => hdiv p hp hpm ?_⟩
        rintro rfl
        obtain ⟨c, hc⟩ := hpm
        have := Nat.odd_iff.1 hmo
        omega
    · have hp1 : ∀ p, p.Prime → ¬ p ∣ 1 := fun p hp h =>
        by have := Nat.le_of_dvd one_pos h; have := hp.two_le; omega
      interval_cases m
      · exact Or.inl ⟨odd_one, fun p hp h => absurd h (hp1 p hp)⟩
      · exact Or.inr ⟨1, Or.inl rfl, odd_one, fun p hp h => absurd h (hp1 p hp)⟩
  · intro h
    have cond : ¬ 8 ∣ m ∧ ∀ p, p.Prime → p ∣ m → p ≠ 2 → zeros p = 1 := by
      rcases h with ⟨hmo, hp⟩ | ⟨k, hk, hko, hp⟩
      · refine ⟨fun h8 => ?_, fun p hpp hpm _ => hp p hpp hpm⟩
        obtain ⟨c, hc⟩ := h8
        have := Nat.odd_iff.1 hmo
        omega
      · refine ⟨fun h8 => ?_, fun p hpp hpm hp2 => hp p hpp ?_⟩
        · obtain ⟨c, hc⟩ := h8
          have := Nat.odd_iff.1 hko
          omega
        · rcases hk with rfl | rfl
          · rcases (Nat.Prime.dvd_mul hpp).1 hpm with h2 | hk
            · exact absurd (two_of p hpp h2) hp2
            · exact hk
          · rcases (Nat.Prime.dvd_mul hpp).1 hpm with h2 | hk
            · exact absurd (two_of p hpp (hpp.dvd_of_dvd_pow (n := 2) (by simpa using h2))) hp2
            · exact hk
    by_cases hm3 : 3 ≤ m
    · obtain ⟨N, hN, hg⟩ := exists_good m cond.1 cond.2
      exact zeros_one_of_good hm3 hN hg
    · interval_cases m
      · exact zeros_one
      · exact zeros_two

end A053029

open A053029
