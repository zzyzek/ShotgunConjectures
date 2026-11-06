import Mathlib

/-!
# Shevelev's generalized factorials: the first row divisible by `p`

V. Shevelev (OEIS A202367-A202369 and the triangles A202941, A203484, A178473): for `t ≥ 1`
let `Q^(t)_0 = 1` and let `Q^(t)_(m+1)` be the polynomial with
`Q^(t)_(m+1)(n) = ∑_{i=1}^n i^t Q^(t)_m(i)`; `n!^(t)` is the lcm of the denominators of the
coefficients of `Q^(t)_n`, and `C^(t)(n, m) = n!^(t) / (m!^(t) (n-m)!^(t))`.

Definitions.
* `Spoly k` : the Faulhaber polynomial, `(Spoly k).eval n = ∑_{i=1}^n i^k` (`Spoly_eval`).
* `sumOp P` : `(sumOp P).eval n = ∑_{i=1}^n P.eval i` (`sumOp_eval`).
* `shevQ t m` = `Q^(t)_m` (`shevQ_succ_eval`; any family with the same recursion equals it,
  `shevQ_unique`). `shevFact t n` = `n!^(t)`, `shevBinom t n m` = `C^(t)(n, m)`.
* `Zp p` : rationals with denominator prime to `p`; `ZpX p` : polynomials with coefficients there.

Main results (`p` prime).
* Power sums (von Staudt-Clausen from Mathlib): `Spoly_mem` : `Spoly k ∈ ZpX p` for
  `1 ≤ k ≤ 2p-3`, `k ≠ p-1`; `Spoly_not_mem` : `Spoly k ∉ ZpX p` for `k ∈ {p-1, 2p-2, 2p-1}`
  (sum of `i^k` over `i ≤ p` is `-1 mod p` when `(p-1) ∣ k`; top coefficient `1/(2p)`).
* Newton's identity (`newton`): `m Q_m = ∑_{a+b=m, b ≥ 1} Q_a S_{tb}`, proved for the values
  through the power series `∏_i 1/(1 - i^t z)` and its logarithmic derivative.
* `shevelev_threshold` : if `r < p`, `t s ≤ 2p-3`, `t s ≠ p-1` for `1 ≤ s < r`, and
  `t r ∈ {p-1, 2p-2, 2p-1}`, then `Q_m ∈ ZpX p` for `m < r` and `Q_r ∉ ZpX p`.
* `shevelev_row` : under the same hypotheses, row `r` of `C^(t)` has outer entries `1`, inner
  entries with `v_p ≥ 1` (so `≠ 1`), and any integer equal to the row sum is `2 mod p`.
-/

namespace OpenProblemsLib.ShevelevFactorial

open Polynomial Finset

theorem ite_of_pos {α : Type*} {c : Prop} [Decidable c] (a b : α) (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_of_not {α : Type*} {c : Prop} [Decidable c] (a b : α) (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-! ## `p`-integral rationals and polynomials -/

section Integral

variable (p : ℕ) [hp : Fact p.Prime]

/-- Rationals whose denominator is prime to `p`. -/
def Zp : Subring ℚ where
  carrier := {q | ¬ p ∣ q.den}
  mul_mem' := by
    intro a b ha hb h
    exact (hp.out.dvd_mul.mp (h.trans (Rat.mul_den_dvd a b))).elim ha hb
  one_mem' := fun h => hp.out.not_dvd_one (by simpa using h)
  add_mem' := by
    intro a b ha hb h
    exact (hp.out.dvd_mul.mp (h.trans (Rat.add_den_dvd a b))).elim ha hb
  zero_mem' := fun h => hp.out.not_dvd_one (by simpa using h)
  neg_mem' := by
    intro a ha
    simpa [Rat.neg_den] using ha

variable {p}

theorem mem_Zp {q : ℚ} : q ∈ Zp p ↔ ¬ p ∣ q.den := Iff.rfl

theorem inv_natCast_mem {a : ℕ} (ha : ¬ p ∣ a) : (a : ℚ)⁻¹ ∈ Zp p := by
  rw [mem_Zp, Rat.inv_natCast_den]
  split_ifs with h
  · exact hp.out.not_dvd_one
  · exact ha

theorem natCast_mem (a : ℕ) : (a : ℚ) ∈ Zp p := _root_.natCast_mem (Zp p) a

theorem intCast_mem (a : ℤ) : (a : ℚ) ∈ Zp p := _root_.intCast_mem (Zp p) a

/-- An integer that is `p` times a `p`-integral rational is divisible by `p`. -/
theorem int_dvd_of_eq_mul {N : ℤ} {z : ℚ} (hz : z ∈ Zp p) (h : (N : ℚ) = p * z) :
    (p : ℤ) ∣ N := by
  have h1 : z * z.den = z.num := Rat.mul_den_eq_num z
  have h2 : (N * z.den : ℤ) = p * z.num := by
    have : ((N * z.den : ℤ) : ℚ) = ((p * z.num : ℤ) : ℚ) := by
      push_cast
      rw [h, ← h1]
      ring
    exact_mod_cast this
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  rcases hpz.dvd_or_dvd (Dvd.intro _ h2.symm) with h3 | h3
  · exact h3
  · exact absurd (Int.natCast_dvd_natCast.mp h3) hz

variable (p)

/-- Polynomials with coefficients in `Zp p`. -/
def ZpX : Subring ℚ[X] where
  carrier := {P | ∀ n, P.coeff n ∈ Zp p}
  mul_mem' := by
    intro a b ha hb n
    rw [coeff_mul]
    exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (ha _) (hb _)
  one_mem' := by
    intro n
    rw [coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' := by
    intro a b ha hb n
    rw [coeff_add]
    exact Subring.add_mem _ (ha n) (hb n)
  zero_mem' := fun n => by simp
  neg_mem' := by
    intro a ha n
    rw [coeff_neg]
    exact Subring.neg_mem _ (ha n)

variable {p}

theorem mem_ZpX {P : ℚ[X]} : P ∈ ZpX p ↔ ∀ n, P.coeff n ∈ Zp p := Iff.rfl

theorem C_mem {c : ℚ} (hc : c ∈ Zp p) : C c ∈ ZpX p := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · exact Subring.zero_mem _

theorem X_mem : (X : ℚ[X]) ∈ ZpX p := by
  intro n
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/-- Values of a `p`-integral polynomial at integers: `P(a) - P(b) = (a - b) z`, `z ∈ Zp p`. -/
theorem eval_sub_eq_mul {P : ℚ[X]} (hP : P ∈ ZpX p) (a b : ℤ) :
    ∃ z ∈ Zp p, P.eval (a : ℚ) - P.eval (b : ℚ) = (a - b) * z := by
  have hl : P ∈ lifts (Zp p).subtype :=
    (lifts_iff_coeff_lifts P).mpr fun n => ⟨⟨_, hP n⟩, rfl⟩
  obtain ⟨P', rfl⟩ := (mem_lifts P).mp hl
  obtain ⟨w, hw⟩ := sub_dvd_eval_sub (a : Zp p) (b : Zp p) P'
  refine ⟨w, w.2, ?_⟩
  have e : ∀ c : ℤ, (P'.map (Zp p).subtype).eval (c : ℚ) = ((P'.eval (c : Zp p) : Zp p) : ℚ) := by
    intro c
    rw [eval_map, ← map_intCast (Zp p).subtype c, eval₂_at_apply]
    rfl
  rw [e, e]
  have := congrArg Subtype.val hw
  push_cast at this
  exact this

/-- `p ∤ lcm of the coefficient denominators` iff the polynomial is `p`-integral. -/
theorem not_dvd_lcm_den_iff (P : ℚ[X]) :
    ¬ p ∣ P.support.lcm (fun i => (P.coeff i).den) ↔ P ∈ ZpX p := by
  constructor
  · intro h n
    by_cases hn : P.coeff n = 0
    · rw [hn]
      exact Subring.zero_mem _
    · intro hd
      exact h (hd.trans (Finset.dvd_lcm (mem_support_iff.mpr hn)))
  · intro h hd
    have h2 : P.support.lcm (fun i => (P.coeff i).den) ∣ ∏ i ∈ P.support, (P.coeff i).den :=
      Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi
    obtain ⟨i, _, hi⟩ := (Prime.dvd_finsetProd_iff hp.out.prime _).mp (hd.trans h2)
    exact h i hi

theorem lcm_den_ne_zero (P : ℚ[X]) : P.support.lcm (fun i => (P.coeff i).den) ≠ 0 := by
  intro h0
  have h2 : P.support.lcm (fun i => (P.coeff i).den) ∣ ∏ i ∈ P.support, (P.coeff i).den :=
    Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi
  rw [h0, zero_dvd_iff, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, _, hi⟩ := h2
  exact (P.coeff i).den_nz hi

end Integral

/-! ## Faulhaber polynomials and their `p`-integrality -/

/-- Faulhaber's polynomial for `∑_{i=1}^n i^k`. -/
noncomputable def Spoly (k : ℕ) : ℚ[X] :=
  ∑ j ∈ range (k + 1), C (bernoulli' j * (k + 1).choose j / (k + 1)) * X ^ (k + 1 - j)

theorem Spoly_eval (k n : ℕ) : (Spoly k).eval (n : ℚ) = ∑ i ∈ Icc 1 n, (i : ℚ) ^ k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_pow, Spoly, eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem Spoly_coeff_top (k : ℕ) : (Spoly k).coeff (k + 1) = 1 / (k + 1) := by
  rw [Spoly, finsetSum_coeff, sum_eq_single 0]
  · simp [bernoulli'_zero]
  · intro j hj hj0
    rw [coeff_C_mul_X_pow, ite_of_not _ _]
    have := mem_range.mp hj
    omega
  · intro h
    simp at h

section Bern

variable {p : ℕ} [hp : Fact p.Prime]

/-- `p B_(2i)` is `p`-integral, and so is `B_(2i)` when `(p - 1) ∤ 2i` (von Staudt-Clausen). -/
theorem bernoulli_even_mem (i : ℕ) :
    (p : ℚ) * _root_.bernoulli (2 * i) ∈ Zp p ∧ (¬ (p - 1) ∣ 2 * i → _root_.bernoulli (2 * i) ∈ Zp p) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen i
  set s := (range (2 * i + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ 2 * i
  have hB : _root_.bernoulli (2 * i) = z - ∑ q ∈ s, (1 : ℚ) / q := by
    rw [hz]
    ring
  constructor
  · rw [hB, mul_sub, Finset.mul_sum]
    refine Subring.sub_mem _ (Subring.mul_mem _ (natCast_mem _) (intCast_mem _))
      (Subring.sum_mem _ fun q hq => ?_)
    have hq' := (Finset.mem_filter.mp hq).2.1
    by_cases hqp : q = p
    · subst hqp
      rw [mul_one_div_cancel (by exact_mod_cast hq'.ne_zero)]
      exact Subring.one_mem _
    · rw [one_div]
      refine Subring.mul_mem _ (natCast_mem _) (inv_natCast_mem fun hd => hqp ?_)
      exact ((Nat.prime_dvd_prime_iff_eq hp.out hq').mp hd).symm
  · intro hnd
    rw [hB]
    refine Subring.sub_mem _ (intCast_mem _) (Subring.sum_mem _ fun q hq => ?_)
    have hq' := Finset.mem_filter.mp hq
    rw [one_div]
    refine inv_natCast_mem fun hd => hnd ?_
    have := (Nat.prime_dvd_prime_iff_eq hp.out hq'.2.1).mp hd
    subst this
    exact hq'.2.2

omit hp in
theorem not_dvd_of_lt_two_mul {a : ℕ} (h1 : 0 < a) (h2 : a < 2 * p) (h3 : a ≠ p) : ¬ p ∣ a := by
  rintro ⟨c, rfl⟩
  rcases c with _ | _ | c
  · omega
  · omega
  · nlinarith

/-- Coefficients of `Spoly k` are `p`-integral for `1 ≤ k ≤ 2p-3`, `k ≠ p-1`. -/
theorem Spoly_coeff_mem (k j : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * p - 3) (hk3 : k ≠ p - 1)
    (hj : j ≤ k) : bernoulli' j * (k + 1).choose j / (k + 1) ∈ Zp p := by
  have hp2 := hp.out.two_le
  have hk : ¬ p ∣ (k + 1) := not_dvd_of_lt_two_mul (by omega) (by omega) (by omega)
  have hinv : ((k : ℚ) + 1)⁻¹ ∈ Zp p := by
    have := inv_natCast_mem (p := p) hk
    push_cast at this
    exact this
  rw [div_eq_mul_inv]
  refine Subring.mul_mem _ ?_ hinv
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | hodd
  · rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      simp only [add_zero] at hi
      subst hi
      simp
    have hj2 : j = 2 * i := by omega
    rw [hj2, ← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
    by_cases hd : (p - 1) ∣ 2 * i
    · obtain ⟨c, hc⟩ := hd
      have hjp : 2 * i = p - 1 := by
        rcases c with _ | _ | c
        · omega
        · omega
        · have := Nat.mul_le_mul_left (p - 1) (show 2 ≤ c + 1 + 1 by omega)
          omega
      have hch : p ∣ (k + 1).choose (2 * i) :=
        hp.out.dvd_choose (by omega) (by omega) (by omega)
      obtain ⟨c', hc'⟩ := hch
      rw [hc']
      push_cast
      rw [show _root_.bernoulli (2 * i) * (p * c') = (p * _root_.bernoulli (2 * i)) * c' by ring]
      exact Subring.mul_mem _ (bernoulli_even_mem i).1 (natCast_mem _)
    · exact Subring.mul_mem _ ((bernoulli_even_mem i).2 hd) (natCast_mem _)
  · rcases Nat.lt_or_ge 1 j with hj1 | hj1
    · rw [bernoulli'_eq_zero_of_odd hodd hj1, zero_mul]
      exact Subring.zero_mem _
    · have : j = 1 := by
        obtain ⟨i, hi⟩ := hodd
        omega
      subst this
      have hp2' : p ≠ 2 := by
        intro h2
        subst h2
        omega
      rw [bernoulli'_one, one_div]
      refine Subring.mul_mem _ (inv_natCast_mem (a := 2) ?_) (natCast_mem _)
      intro hd
      exact hp2' ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)

/-- `S_k ∈ ℤ_(p)[x]` for `1 ≤ k ≤ 2p-3`, `k ≠ p-1`. -/
theorem Spoly_mem (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * p - 3) (hk3 : k ≠ p - 1) :
    Spoly k ∈ ZpX p := by
  refine Subring.sum_mem _ fun j hj => Subring.mul_mem _ (C_mem ?_) (Subring.pow_mem _ X_mem _)
  exact Spoly_coeff_mem k j hk1 hk2 hk3 (Nat.lt_succ_iff.mp (mem_range.mp hj))

/-- `∑_{i=1}^p i^k ≢ 0 (mod p)` when `(p - 1) ∣ k`, `k ≥ 1`. -/
theorem sum_pow_not_dvd (k : ℕ) (hk : 1 ≤ k) (hd : (p - 1) ∣ k) :
    ¬ (p : ℤ) ∣ ((∑ i ∈ Icc 1 p, i ^ k : ℕ) : ℤ) := by
  have hp2 := hp.out.two_le
  intro h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  push_cast at h
  obtain ⟨c, rfl⟩ := hd
  have hsplit : Icc 1 p = insert p (Icc 1 (p - 1)) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  rw [hsplit, sum_insert (by simp; omega), ZMod.natCast_self, zero_pow (by omega), zero_add] at h
  have hone : ∀ i ∈ Icc 1 (p - 1), ((i : ℕ) : ZMod p) ^ ((p - 1) * c) = 1 := by
    intro i hi
    have hi' := mem_Icc.mp hi
    have hne : ((i : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [pow_mul, ZMod.pow_card_sub_one_eq_one hne, one_pow]
  rw [sum_congr rfl hone, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
    ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

/-- `S_k ∉ ℤ_(p)[x]` for `k ∈ {p-1, 2p-2, 2p-1}`. -/
theorem Spoly_not_mem (k : ℕ) (hk : k = p - 1 ∨ k = 2 * p - 2 ∨ k = 2 * p - 1) :
    Spoly k ∉ ZpX p := by
  have hp2 := hp.out.two_le
  intro hS
  rcases hk with hk | hk | hk
  rotate_right
  · have h := hS (k + 1)
    rw [Spoly_coeff_top, mem_Zp] at h
    apply h
    have e : (1 : ℚ) / ((k : ℚ) + 1) = ((2 * p : ℕ) : ℚ)⁻¹ := by
      have hk' : k + 1 = 2 * p := by omega
      rw [one_div, show ((k : ℚ) + 1) = ((2 * p : ℕ) : ℚ) by exact_mod_cast hk']
    rw [e, Rat.inv_natCast_den, ite_of_not _ _ (by omega)]
    exact dvd_mul_left p 2
  all_goals
    have hk1 : 1 ≤ k := by omega
    have hd : (p - 1) ∣ k := by
      subst hk
      first
        | exact dvd_refl _
        | exact ⟨2, by omega⟩
    obtain ⟨z, hz, he⟩ := eval_sub_eq_mul hS (p : ℤ) 0
    have e0 : (Spoly k).eval ((0 : ℤ) : ℚ) = 0 := by
      have := Spoly_eval k 0
      push_cast at this ⊢
      rw [this]
      simp
    have ep : (Spoly k).eval (((p : ℤ)) : ℚ) = (((∑ i ∈ Icc 1 p, i ^ k : ℕ) : ℤ) : ℚ) := by
      have := Spoly_eval k p
      push_cast at this ⊢
      exact this
    rw [e0, ep, sub_zero] at he
    have := int_dvd_of_eq_mul (N := ((∑ i ∈ Icc 1 p, i ^ k : ℕ) : ℤ)) hz
      (by rw [he]; push_cast; ring)
    exact sum_pow_not_dvd k hk1 hd this

end Bern

/-! ## The polynomials `Q^(t)_m` -/

/-- Summation operator: `(sumOp P).eval n = ∑_{i=1}^n P.eval i`. -/
noncomputable def sumOp (P : ℚ[X]) : ℚ[X] := P.sum fun k c => C c * Spoly k

theorem sumOp_eval (P : ℚ[X]) (n : ℕ) :
    (sumOp P).eval (n : ℚ) = ∑ i ∈ Icc 1 n, P.eval (i : ℚ) := by
  simp only [sumOp, Polynomial.sum, eval_finsetSum, eval_mul, eval_C, Spoly_eval,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_eq_sum, Polynomial.sum]

/-- Shevelev's `Q^(t)_m`. -/
noncomputable def shevQ (t : ℕ) : ℕ → ℚ[X]
  | 0 => 1
  | m + 1 => sumOp (X ^ t * shevQ t m)

theorem shevQ_zero (t : ℕ) : shevQ t 0 = 1 := rfl

/-- The defining recursion `Q_(m+1)(n) = ∑_{i=1}^n i^t Q_m(i)`. -/
theorem shevQ_succ_eval (t m n : ℕ) :
    (shevQ t (m + 1)).eval (n : ℚ) = ∑ i ∈ Icc 1 n, (i : ℚ) ^ t * (shevQ t m).eval (i : ℚ) := by
  simp [shevQ, sumOp_eval]

theorem poly_eq_of_eval_nat {P R : ℚ[X]} (h : ∀ n : ℕ, P.eval (n : ℚ) = R.eval (n : ℚ)) :
    P = R := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (Nat.cast : ℕ → ℚ))
  · rintro _ ⟨n, rfl⟩
    exact h n
  · exact Set.infinite_range_of_injective Nat.cast_injective

/-- Any family with `Q_0 = 1` and Shevelev's recursion is `shevQ t`. -/
theorem shevQ_unique (t : ℕ) (Q : ℕ → ℚ[X]) (h0 : Q 0 = 1)
    (hs : ∀ m n : ℕ, (Q (m + 1)).eval (n : ℚ) = ∑ i ∈ Icc 1 n, (i : ℚ) ^ t * (Q m).eval (i : ℚ)) :
    Q = shevQ t := by
  funext m
  induction m with
  | zero => exact h0
  | succ m ih => exact poly_eq_of_eval_nat fun n => by rw [hs, shevQ_succ_eval, ih]

/-- Shevelev's generalized factorial `n!^(t)`. -/
noncomputable def shevFact (t n : ℕ) : ℕ :=
  (shevQ t n).support.lcm fun i => ((shevQ t n).coeff i).den

/-- Shevelev's generalized binomial `C^(t)(n, m) = n!^(t) / (m!^(t) (n-m)!^(t))`. -/
noncomputable def shevBinom (t n m : ℕ) : ℚ :=
  (shevFact t n : ℚ) / ((shevFact t m : ℚ) * (shevFact t (n - m) : ℚ))

theorem shevFact_ne_zero (t n : ℕ) : shevFact t n ≠ 0 := lcm_den_ne_zero _

theorem shevFact_zero (t : ℕ) : shevFact t 0 = 1 := by
  refine Nat.dvd_one.mp (Finset.lcm_dvd fun i _ => ?_)
  rw [shevQ_zero, coeff_one]
  split_ifs <;> simp

/-! ## Newton's identity -/

section Newton

open PowerSeries in
/-- `z d/dz`. -/
noncomputable def theta (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (m : ℚ) * PowerSeries.coeff m f

theorem theta_mul (f g : PowerSeries ℚ) : theta (f * g) = theta f * g + f * theta g := by
  ext m
  simp only [theta, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine sum_congr rfl fun x hx => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [← h]
  push_cast
  ring

/-- `∑_j y^j z^j = 1/(1 - y z)`. -/
noncomputable def geo (y : ℚ) : PowerSeries ℚ := PowerSeries.mk fun j => y ^ j

theorem theta_geo (y : ℚ) : theta (geo y) = geo y * (geo y - 1) := by
  ext m
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul]
  simp only [theta, geo, PowerSeries.coeff_mk]
  have : ∀ x ∈ antidiagonal m, y ^ x.1 * y ^ x.2 = y ^ m := by
    intro x hx
    rw [← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hx]
  rw [sum_congr rfl this, sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  push_cast
  ring

theorem geo_mul (y : ℚ) : (1 - PowerSeries.C y * PowerSeries.X) * geo y = 1 := by
  ext m
  rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
  rcases m with _ | m
  · simp [geo]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [geo, pow_succ]
    ring

/-- `∑_m Q_m(n) z^m`. -/
noncomputable def Hser (t n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (shevQ t m).eval (n : ℚ)

theorem Hser_zero (t : ℕ) : Hser t 0 = 1 := by
  ext m
  rcases m with _ | m
  · simp [Hser, shevQ_zero]
  · simpa [Hser] using shevQ_succ_eval t m 0

theorem Hser_succ (t n : ℕ) : Hser t (n + 1) = Hser t n * geo (((n + 1 : ℕ) : ℚ) ^ t) := by
  set y : ℚ := ((n + 1 : ℕ) : ℚ) ^ t
  have h1 : Hser t (n + 1) * (1 - PowerSeries.C y * PowerSeries.X) = Hser t n := by
    ext m
    rw [mul_sub, mul_one, map_sub, mul_comm, mul_assoc, PowerSeries.coeff_C_mul]
    rcases m with _ | m
    · simp [Hser, shevQ_zero]
    · rw [PowerSeries.coeff_succ_X_mul]
      simp only [Hser, PowerSeries.coeff_mk]
      rw [shevQ_succ_eval, shevQ_succ_eval, Finset.sum_Icc_succ_top (by omega)]
      ring
  calc Hser t (n + 1)
      = Hser t (n + 1) * ((1 - PowerSeries.C y * PowerSeries.X) * geo y) := by
        rw [geo_mul, mul_one]
    _ = Hser t n * geo y := by rw [← mul_assoc, h1]

/-- `∑_r S_(t r)(n) z^r` (no constant term). -/
noncomputable def Pser (t n : ℕ) : PowerSeries ℚ :=
  ∑ i ∈ Icc 1 n, (geo ((i : ℚ) ^ t) - 1)

theorem newton_series (t n : ℕ) : theta (Hser t n) = Hser t n * Pser t n := by
  induction n with
  | zero =>
    rw [Hser_zero, Pser]
    ext m
    simp [theta, PowerSeries.coeff_one]
  | succ n ih =>
    have e : Pser t (n + 1) = Pser t n + (geo (((n + 1 : ℕ) : ℚ) ^ t) - 1) := by
      rw [Pser, Pser, Finset.sum_Icc_succ_top (by omega)]
    rw [Hser_succ, theta_mul, ih, theta_geo, e]
    ring

theorem coeff_Pser (t n b : ℕ) :
    PowerSeries.coeff b (Pser t n) = if b = 0 then 0 else (Spoly (t * b)).eval (n : ℚ) := by
  rw [Pser, map_sum, Spoly_eval]
  split_ifs with hb
  · subst hb
    simp [geo]
  · refine sum_congr rfl fun i _ => ?_
    simp [geo, PowerSeries.coeff_one, hb, pow_mul]

/-- `S_(t b)` for `b ≥ 1`, and `0` for `b = 0`. -/
noncomputable def Shat (t b : ℕ) : ℚ[X] := if b = 0 then 0 else Spoly (t * b)

/-- Newton's identity `m Q_m = ∑_{a+b=m} Q_a Ŝ_b`. -/
theorem newton (t m : ℕ) :
    C (m : ℚ) * shevQ t m = ∑ x ∈ antidiagonal m, shevQ t x.1 * Shat t x.2 := by
  apply poly_eq_of_eval_nat
  intro n
  have h := congrArg (PowerSeries.coeff m) (newton_series t n)
  rw [PowerSeries.coeff_mul] at h
  simp only [theta, Hser, PowerSeries.coeff_mk, coeff_Pser] at h
  rw [eval_mul, eval_C, h, eval_finsetSum]
  refine sum_congr rfl fun x _ => ?_
  rw [eval_mul, Shat]
  split_ifs <;> simp

end Newton

/-! ## The threshold -/

section Threshold

variable {p : ℕ} [hp : Fact p.Prime]

theorem shevelev_threshold (t r : ℕ) (ht : 1 ≤ t) (hr : r < p)
    (hlow : ∀ s, 1 ≤ s → s < r → t * s ≤ 2 * p - 3 ∧ t * s ≠ p - 1)
    (htop : t * r = p - 1 ∨ t * r = 2 * p - 2 ∨ t * r = 2 * p - 1) :
    (∀ m < r, shevQ t m ∈ ZpX p) ∧ shevQ t r ∉ ZpX p := by
  have hlow' : ∀ s, 1 ≤ s → s < r → Shat t s ∈ ZpX p := by
    intro s hs1 hs2
    rw [Shat, ite_of_not _ _ (by omega)]
    obtain ⟨h1, h2⟩ := hlow s hs1 hs2
    exact Spoly_mem _ (Nat.one_le_iff_ne_zero.mpr (by positivity)) h1 h2
  have hlowm : ∀ m < r, shevQ t m ∈ ZpX p := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        exact Subring.one_mem _
      have hsum : C (m : ℚ) * shevQ t m ∈ ZpX p := by
        rw [newton]
        refine Subring.sum_mem _ fun x hx => ?_
        have hab := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        by_cases hb : x.2 = 0
        · rw [Shat, ite_of_pos _ _ hb, mul_zero]
          exact Subring.zero_mem _
        · exact Subring.mul_mem _ (ih x.1 (by omega) (by omega)) (hlow' x.2 (by omega) (by omega))
      have hinv : C ((m : ℚ)⁻¹) ∈ ZpX p :=
        C_mem (inv_natCast_mem (Nat.not_dvd_of_pos_of_lt h0 (by omega)))
      have e : shevQ t m = C ((m : ℚ)⁻¹) * (C (m : ℚ) * shevQ t m) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (by exact_mod_cast h0.ne'), C_1, one_mul]
      rw [e]
      exact Subring.mul_mem _ hinv hsum
  refine ⟨hlowm, fun hQ => ?_⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := hp.out.two_le
    omega
  have hmem : ((0 : ℕ), r) ∈ antidiagonal r := Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add r)
  have hN := newton t r
  rw [← Finset.add_sum_erase _ _ hmem, shevQ_zero, Shat, ite_of_not _ _ hr0, one_mul] at hN
  have hrest : ∑ x ∈ (antidiagonal r).erase (0, r), shevQ t x.1 * Shat t x.2 ∈ ZpX p := by
    refine Subring.sum_mem _ fun x hx => ?_
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    have hab := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    by_cases hb : x.2 = 0
    · rw [Shat, ite_of_pos _ _ hb, mul_zero]
      exact Subring.zero_mem _
    · have ha : x.1 ≠ 0 := by
        intro ha
        apply hne
        ext <;> simp <;> omega
      exact Subring.mul_mem _ (hlowm x.1 (by omega)) (hlow' x.2 (by omega) (by omega))
  have hS : Spoly (t * r) ∈ ZpX p := by
    have e : Spoly (t * r) = C (r : ℚ) * shevQ t r -
        ∑ x ∈ (antidiagonal r).erase (0, r), shevQ t x.1 * Shat t x.2 := by
      rw [hN]
      ring
    rw [e]
    exact Subring.sub_mem _ (Subring.mul_mem _ (C_mem (natCast_mem _)) hQ) hrest
  exact Spoly_not_mem _ htop hS

/-- `v_p(m!^(t)) = 0` for `m < r` and `p ∣ r!^(t)`. -/
theorem shevFact_threshold (t r : ℕ) (ht : 1 ≤ t) (hr : r < p)
    (hlow : ∀ s, 1 ≤ s → s < r → t * s ≤ 2 * p - 3 ∧ t * s ≠ p - 1)
    (htop : t * r = p - 1 ∨ t * r = 2 * p - 2 ∨ t * r = 2 * p - 1) :
    (∀ m < r, ¬ p ∣ shevFact t m) ∧ p ∣ shevFact t r := by
  obtain ⟨h1, h2⟩ := shevelev_threshold t r ht hr hlow htop
  refine ⟨fun m hm => (not_dvd_lcm_den_iff _).mpr (h1 m hm), ?_⟩
  by_contra h
  exact h2 ((not_dvd_lcm_den_iff _).mp h)

/-- Row `r` of `C^(t)`: outer entries `1`, inner entries with `v_p ≥ 1` (so `≠ 1`), and an integer
equal to the row sum is `2 mod p`. -/
theorem shevelev_row (t r : ℕ) (ht : 1 ≤ t) (hr : r < p)
    (hlow : ∀ s, 1 ≤ s → s < r → t * s ≤ 2 * p - 3 ∧ t * s ≠ p - 1)
    (htop : t * r = p - 1 ∨ t * r = 2 * p - 2 ∨ t * r = 2 * p - 1) :
    shevBinom t r 0 = 1 ∧ shevBinom t r r = 1 ∧
    (∀ m, 0 < m → m < r → 1 ≤ padicValRat p (shevBinom t r m) ∧ shevBinom t r m ≠ 1) ∧
    (∀ N : ℤ, (N : ℚ) = ∑ m ∈ range (r + 1), shevBinom t r m → (p : ℤ) ∣ N - 2) := by
  obtain ⟨hlo, hdv⟩ := shevFact_threshold t r ht hr hlow htop
  have hp2 := hp.out.two_le
  have hr0 : r ≠ 0 := by
    rintro rfl
    omega
  have hne : ∀ n, (shevFact t n : ℚ) ≠ 0 := fun n => by exact_mod_cast shevFact_ne_zero t n
  have hout0 : shevBinom t r 0 = 1 := by
    rw [shevBinom, shevFact_zero, Nat.sub_zero]
    push_cast
    rw [one_mul, div_self (hne r)]
  have houtr : shevBinom t r r = 1 := by
    rw [shevBinom, Nat.sub_self, shevFact_zero]
    push_cast
    rw [mul_one, div_self (hne r)]
  obtain ⟨c, hc⟩ := hdv
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact shevFact_ne_zero t r (by rw [hc, mul_zero])
  -- Inner entries are `p` times a `p`-integral rational.
  --
  have hin : ∀ m, 0 < m → m < r →
      shevBinom t r m = p * ((c : ℚ) * ((shevFact t m : ℚ)⁻¹ * (shevFact t (r - m) : ℚ)⁻¹)) ∧
      (c : ℚ) * ((shevFact t m : ℚ)⁻¹ * (shevFact t (r - m) : ℚ)⁻¹) ∈ Zp p := by
    intro m _ hm
    constructor
    · rw [shevBinom, hc]
      push_cast
      field_simp
    · exact Subring.mul_mem _ (natCast_mem _) (Subring.mul_mem _
        (inv_natCast_mem (hlo m hm)) (inv_natCast_mem (hlo (r - m) (by omega))))
  refine ⟨hout0, houtr, fun m hm0 hm => ⟨?_, ?_⟩, fun N hN => ?_⟩
  · have hpc : ((p * c : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hp.out.ne_zero hc0
    rw [shevBinom, hc, padicValRat.div hpc (mul_ne_zero (hne m) (hne (r - m))),
      padicValRat.mul (hne m) (hne (r - m)), padicValRat.of_nat, padicValRat.of_nat,
      padicValRat.of_nat, padicValNat.mul hp.out.ne_zero hc0, padicValNat.self hp.out.one_lt,
      padicValNat.eq_zero_of_not_dvd (hlo m hm),
      padicValNat.eq_zero_of_not_dvd (hlo (r - m) (by omega))]
    have h1 : 0 ≤ padicValRat p (c : ℚ) := by
      rw [padicValRat.of_nat]
      positivity
    push_cast
    linarith
  · intro h1
    have h := (hin m hm0 hm).1
    have hz := (hin m hm0 hm).2
    rw [h1] at h
    have := int_dvd_of_eq_mul (N := 1) hz (by push_cast; exact h)
    have := Int.eq_one_of_dvd_one (by positivity) this
    omega
  · have hsplit : ∑ m ∈ range (r + 1), shevBinom t r m =
        2 + ∑ m ∈ Ioo 0 r, shevBinom t r m := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hout0,
        Finset.sum_Ico_succ_top (by omega), houtr, Finset.Ico_add_one_left_eq_Ioo]
      ring
    have hz : ∑ m ∈ Ioo 0 r, (c : ℚ) * ((shevFact t m : ℚ)⁻¹ * (shevFact t (r - m) : ℚ)⁻¹)
        ∈ Zp p := Subring.sum_mem _ fun m hm => by
      have := Finset.mem_Ioo.mp hm
      exact (hin m this.1 this.2).2
    apply int_dvd_of_eq_mul hz
    push_cast
    rw [hN, hsplit, add_sub_cancel_left, Finset.mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have := Finset.mem_Ioo.mp hm
    exact (hin m this.1 this.2).1

end Threshold

end OpenProblemsLib.ShevelevFactorial
