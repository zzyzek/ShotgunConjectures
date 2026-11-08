import Mathlib

/-!
# OEIS A228885: det [ [gcd(i + j, n) = 1] ]_{1 ≤ i, j ≤ n}

`a228885 n` is the determinant of the `n × n` 0/1 matrix with entry `1` when `i + j` is coprime
to `n` (`1 ≤ i, j ≤ n`).

Proved here, for squarefree `n ≥ 1`:
* `A228885_formula`: Oudra's formula `a(n) = (-1)^⌊n/2⌋ ∏_{d ∣ n} φ(d)^φ(n/d)`.
* `A228885_sign`: Sun's conjecture `(-1)^(n(n-1)/2) a(n) > 0`.

Route: `det_hankel_zmod` (a matrix `v(x + y + 2)` over `ZMod n` has determinant
`sign(x ↦ -x) · ∏_k ∑_m v m e(-m k)`), `eig_ram` (the eigenvalues of the coprimality indicator are
the Ramanujan sums `ram n k`), `ram_squarefree` (von Sterneck for squarefree `n`:
`c_n(k) = μ(n/g) φ(g)`, `g = gcd(k, n)`), `sign_neg_zmod` and `prod_mu_sign` (fixed points of
`x ↦ -x` are `0` and, for even `n`, `n/2`), `prod_totient_gcd` (Oudra's product).

Outside Lean: none (reading the OEIS definition as `a228885` is the only step not checked).
-/

open Finset Matrix

section Hankel

variable (n : ℕ) [NeZero n]

/-- `∏_k e(k)` is `±1`: its square is `1`. -/
lemma prod_stdAddChar_sq :
    (∏ k : ZMod n, (ZMod.stdAddChar (-k) : ℂ)) ^ 2 = 1 := by
  set e := (ZMod.stdAddChar : AddChar (ZMod n) ℂ)
  set P := ∏ k : ZMod n, e k
  have hP : ∏ k : ZMod n, e (-k) = P :=
    Fintype.prod_equiv (Equiv.neg (ZMod n)) _ _ (fun k => rfl)
  have hinv : ∏ k : ZMod n, e (-k) = P⁻¹ := by
    rw [← prod_inv_distrib]
    exact prod_congr rfl fun k _ => AddChar.map_neg_eq_inv e k
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 fun k _ => by
    intro h
    have := AddChar.map_neg_eq_inv e k
    have h2 : e k * e (-k) = 1 := by rw [← AddChar.map_add_eq_mul]; simp
    rw [h, zero_mul] at h2; exact zero_ne_one h2
  rw [hP, sq]
  have : P = P⁻¹ := hP.symm.trans hinv
  calc P * P = P * P⁻¹ := by rw [← this]
    _ = 1 := mul_inv_cancel₀ hP0

/-- Determinant of the Hankel-type matrix `v(x + y + 2)` over `ZMod n`: the sign of `x ↦ -x`
times the product of the DFT eigenvalues of `v`. -/
theorem det_hankel_zmod (v : ZMod n → ℂ) :
    (Matrix.of fun x y : ZMod n => v (x + y + 2)).det =
      (Equiv.Perm.sign (Equiv.neg (ZMod n)) : ℂ) *
        ∏ k : ZMod n, ∑ m : ZMod n, v m * ZMod.stdAddChar (-(m * k)) := by
  set e := (ZMod.stdAddChar : AddChar (ZMod n) ℂ) with he
  have hprim := ZMod.isPrimitive_stdAddChar n
  let F : Matrix (ZMod n) (ZMod n) ℂ := Matrix.of fun j k => e (j * k)
  let G : Matrix (ZMod n) (ZMod n) ℂ := Matrix.of fun k l => e (-(k * l))
  have hFG : F * G = (n : ℂ) • (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
    ext j l
    simp only [F, G, mul_apply, of_apply, Matrix.smul_apply, Matrix.one_apply]
    have : ∀ k, e (j * k) * e (-(k * l)) = e (k * (j - l)) := fun k => by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    simp_rw [this]
    rw [AddChar.sum_mulShift _ hprim, ZMod.card]
    by_cases h : j = l
    · simp [h]
    · simp [h, sub_ne_zero.2 h]
  have hFdet : F.det ≠ 0 := by
    intro h0
    have := congrArg det hFG
    rw [det_mul, h0, zero_mul, det_smul, det_one, mul_one, ZMod.card] at this
    exact (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n))) this.symm
  set ν : ZMod n → ℂ := fun k => ∑ m, v m * e (m * k) with hν
  have hMF : (Matrix.of fun x y : ZMod n => v (x + y + 2)) * F =
      F.submatrix id (Equiv.neg (ZMod n)) * diagonal (fun k => e (-(2 * k)) * ν k) := by
    ext x k
    rw [mul_diagonal]
    simp only [F, mul_apply, of_apply, submatrix_apply, id, Equiv.neg_apply, hν]
    rw [mul_sum, mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (x + 2)) _ _ (fun y => ?_)
    simp only [Equiv.coe_addRight]
    rw [show y + (x + 2) = x + y + 2 by ring]
    rw [mul_left_comm, ← mul_assoc, ← AddChar.map_add_eq_mul, mul_left_comm,
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have h1 := congrArg det hMF
  rw [det_mul, det_mul, det_permute', det_diagonal, prod_mul_distrib] at h1
  have hprod2 : ∏ k : ZMod n, e (-(2 * k)) = 1 := by
    have : ∏ k : ZMod n, e (-(2 * k)) = (∏ k : ZMod n, e (-k)) ^ 2 := by
      rw [sq, ← prod_mul_distrib]
      exact prod_congr rfl fun k _ => by rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this, prod_stdAddChar_sq]
  have hν' : ∏ k : ZMod n, ν k = ∏ k : ZMod n, ∑ m, v m * e (-(m * k)) :=
    Fintype.prod_equiv (Equiv.neg (ZMod n)) _ _ (fun k => by
      simp only [hν, Equiv.neg_apply]
      exact sum_congr rfl fun m _ => by rw [mul_neg, neg_neg])
  rw [hprod2, one_mul, hν'] at h1
  have h2 : F.det * (Matrix.of fun x y : ZMod n => v (x + y + 2)).det =
      F.det * ((Equiv.Perm.sign (Equiv.neg (ZMod n)) : ℂ) *
        ∏ k : ZMod n, ∑ m : ZMod n, v m * e (-(m * k))) := by
    rw [mul_comm F.det, h1]
    ring
  exact mul_left_cancel₀ hFdet h2

/-- Elements of `ZMod n` whose value is a multiple of `d`, for `d ∣ n`: there are `n / d`. -/
lemma card_filter_dvd_val {d : ℕ} (hd : d ∣ n) :
    (univ.filter fun m : ZMod n => d ∣ m.val).card = n / d := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← Nat.Ioc_filter_dvd_card_eq_div n d]
  refine card_nbij' (fun m => n - m.val) (fun x => ((n - x : ℕ) : ZMod n)) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hm
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq]
    have := ZMod.val_lt m
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact Nat.dvd_sub hd hm
  · intro x hx
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [ZMod.val_cast_of_lt (by omega)]
    exact Nat.dvd_sub hd hx.2
  · intro m _
    simp only
    rw [show n - (n - m.val) = m.val by have := ZMod.val_lt m; omega, ZMod.natCast_zmod_val]
  · intro x hx
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hx
    simp only
    rw [ZMod.val_cast_of_lt (by omega)]
    omega

/-- The character sum over multiples of `d` (with `d ∣ n`). -/
lemma charsum_dvd {d : ℕ} (hd : d ∣ n) (k : ZMod n) :
    (∑ m : ZMod n, if d ∣ m.val then ZMod.stdAddChar (-(m * k)) else (0 : ℂ)) =
      if (n / d) ∣ k.val then ((n / d : ℕ) : ℂ) else 0 := by
  set e := (ZMod.stdAddChar : AddChar (ZMod n) ℂ) with he
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  obtain ⟨q, hq⟩ := hd
  have hqd : n / d = q := by rw [hq, Nat.mul_div_cancel_left _ hd0]
  rw [hqd]
  have hzero : ∀ x : ℕ, ((x : ℕ) : ZMod n) = 0 ↔ n ∣ x := fun x => ZMod.natCast_eq_zero_iff x n
  have hmk : ∀ m k : ZMod n, m * k = ((m.val * k.val : ℕ) : ZMod n) := fun m k => by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  by_cases hk : q ∣ k.val
  · rw [ite_eq_left hk]
    have : ∀ m : ZMod n, (if d ∣ m.val then e (-(m * k)) else 0) =
        if d ∣ m.val then (1 : ℂ) else 0 := by
      intro m
      split_ifs with hm
      · have : m * k = 0 := by
          rw [hmk, hzero]
          have := Nat.mul_dvd_mul hm hk
          rwa [← hq] at this
        rw [this, neg_zero, AddChar.map_zero_eq_one]
      · rfl
    rw [sum_congr rfl fun m _ => this m, sum_boole, card_filter_dvd_val n ⟨q, hq⟩, hqd]
  · rw [ite_eq_right hk]
    set T := ∑ m : ZMod n, if d ∣ m.val then e (-(m * k)) else 0 with hT
    have hshift : T = T * e ((d : ZMod n) * k) := by
      rw [hT, sum_mul]
      refine Fintype.sum_equiv (Equiv.addRight (d : ZMod n)) _ _ (fun m => ?_)
      simp only [Equiv.coe_addRight]
      have hval : d ∣ (m + (d : ZMod n)).val ↔ d ∣ m.val := by
        rw [ZMod.val_add, ZMod.val_natCast]
        rw [Nat.dvd_mod_iff ⟨q, hq⟩, Nat.dvd_add_left (Nat.dvd_mod_iff ⟨q, hq⟩ |>.2 dvd_rfl)]
      by_cases hm : d ∣ m.val
      · rw [ite_eq_left hm]
        simp only [hval, hm, ite_true]
        rw [← AddChar.map_add_eq_mul]
        congr 1; ring
      · rw [ite_eq_right hm]
        simp only [hval, hm, ite_false, zero_mul]
    have hne : e ((d : ZMod n) * k) ≠ 1 := by
      intro h1
      rw [← AddChar.map_zero_eq_one e] at h1
      have h2 := ZMod.injective_stdAddChar h1
      rw [show (d : ZMod n) * k = ((d * k.val : ℕ) : ZMod n) by
        push_cast; rw [ZMod.natCast_zmod_val], hzero] at h2
      have h3 : d * q ∣ d * k.val := hq ▸ h2
      exact hk (Nat.dvd_of_mul_dvd_mul_left hd0 h3)
    have : T * (1 - e ((d : ZMod n) * k)) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hne


end Hankel

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

lemma sum_moebius_divisors (g : ℕ) : (∑ d ∈ g.divisors, (μ d : ℤ)) = if g = 1 then 1 else 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f g) (coe_moebius_mul_coe_zeta (R := ℤ))
  simp only [coe_mul_zeta_apply, ArithmeticFunction.one_apply, intCoe_apply, Int.cast_id] at this
  exact this

lemma divisors_gcd (k n : ℕ) (hn : n ≠ 0) :
    (Nat.gcd k n).divisors = n.divisors.filter (· ∣ k) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
  have : Nat.gcd k n ≠ 0 := Nat.gcd_ne_zero_right hn
  tauto

/-- The Ramanujan sum `c_n(k) = ∑_{d ∣ n, (n/d) ∣ k} μ(d) · n/d`. -/
def ram (n k : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, if (n / d) ∣ k then μ d * ((n / d : ℕ) : ℤ) else 0

lemma eig_ram (n : ℕ) [NeZero n] (k : ZMod n) :
    ∑ m : ZMod n, (if Nat.Coprime m.val n then (1 : ℂ) else 0) * ZMod.stdAddChar (-(m * k)) =
      (ram n k.val : ℂ) := by
  have hn : n ≠ 0 := NeZero.ne n
  have hg : ∀ m : ZMod n, (if Nat.Coprime m.val n then (1 : ℂ) else 0) =
      ∑ d ∈ n.divisors, if d ∣ m.val then (μ d : ℂ) else 0 := by
    intro m
    rw [← sum_filter, ← divisors_gcd m.val n hn]
    have := sum_moebius_divisors (Nat.gcd m.val n)
    have h2 : ((∑ d ∈ (Nat.gcd m.val n).divisors, (μ d : ℤ) : ℤ) : ℂ) =
        ∑ d ∈ (Nat.gcd m.val n).divisors, (μ d : ℂ) := by push_cast; rfl
    rw [← h2, this]
    unfold Nat.Coprime
    split_ifs <;> simp
  simp_rw [hg, sum_mul]
  rw [sum_comm]
  unfold ram
  rw [Int.cast_sum]
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have : ∀ m : ZMod n, (if d ∣ m.val then (μ d : ℂ) else 0) * ZMod.stdAddChar (-(m * k)) =
      (μ d : ℂ) * (if d ∣ m.val then ZMod.stdAddChar (-(m * k)) else 0) := by
    intro m; split_ifs <;> simp
  rw [sum_congr rfl fun m _ => this m, ← mul_sum, charsum_dvd n hdn k]
  split_ifs <;> simp only [mul_zero, Int.cast_mul, Int.cast_natCast, Int.cast_zero]

lemma sum_moebius_mul_div (g : ℕ) (hg : 0 < g) :
    ∑ e ∈ g.divisors, (μ (g / e) : ℤ) * e = Nat.totient g := by
  have hinv := (sum_eq_iff_sum_mul_moebius_eq (R := ℤ) (f := fun n => (Nat.totient n : ℤ))
    (g := fun n => (n : ℤ))).1 (fun n _ => by exact_mod_cast Nat.sum_totient n) g hg
  have hinv' : ∑ x ∈ g.divisorsAntidiagonal, (μ x.1 : ℤ) * (x.2 : ℤ) = Nat.totient g := by
    simpa using hinv
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℤ) * (b : ℤ))] at hinv'
  rw [← hinv', ← Nat.sum_div_divisors g]
  refine sum_congr rfl fun d hd => ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hg.ne']

/-- von Sterneck for squarefree `n`: `c_n(k) = μ(n/g) φ(g)`, `g = gcd(k, n)`. -/
lemma ram_squarefree (n k : ℕ) (hn : 0 < n) (hsq : Squarefree n) :
    ram n k = μ (n / Nat.gcd k n) * Nat.totient (Nat.gcd k n) := by
  set g := Nat.gcd k n with hgdef
  have hgn : g ∣ n := Nat.gcd_dvd_right k n
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right k hn
  unfold ram
  rw [← Nat.sum_div_divisors n]
  have e1 : ∀ e ∈ n.divisors, (if n / (n / e) ∣ k then μ (n / e) * ((n / (n / e) : ℕ) : ℤ) else 0) =
      if e ∣ k then μ (n / e) * (e : ℤ) else 0 := by
    intro e he
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hn.ne']
  rw [sum_congr rfl e1, ← sum_filter, ← divisors_gcd k n hn.ne', ← hgdef]
  have e2 : ∀ e ∈ g.divisors, μ (n / e) * (e : ℤ) = μ (n / g) * (μ (g / e) * e) := by
    intro e he
    have heg : e ∣ g := Nat.dvd_of_mem_divisors he
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hsplit : n / e = n / g * (g / e) := by
      obtain ⟨a, ha⟩ := hgn
      obtain ⟨b, hb⟩ := heg
      have hb0 : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · rw [h, mul_zero] at hb; omega
        · exact h
      rw [ha, hb, mul_assoc, Nat.mul_div_cancel_left _ he0, Nat.mul_div_cancel_left _ he0,
        ← mul_assoc, Nat.mul_div_cancel_left _ (by positivity), mul_comm]
    have hcop : Nat.Coprime (n / g) (g / e) :=
      Nat.coprime_of_squarefree_mul (hsplit ▸ hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd
        (heg.trans hgn)))
    rw [hsplit, isMultiplicative_moebius.map_mul_of_coprime hcop]
    ring
  rw [sum_congr rfl e2, ← mul_sum, sum_moebius_mul_div g hg0]

section Signs

variable (n : ℕ) [NeZero n]

lemma neg_eq_self_iff (k : ZMod n) : -k = k ↔ k.val = 0 ∨ 2 * k.val = n := by
  rw [← (ZMod.val_injective n).eq_iff, ZMod.neg_val]
  have := ZMod.val_lt k
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : k.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
    rw [ite_eq_right hk]; omega

lemma fix_filter :
    (univ.filter fun k : ZMod n => -k = k) =
      if 2 ∣ n then {0, ((n / 2 : ℕ) : ZMod n)} else {0} := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  ext k
  simp only [mem_filter, mem_univ, true_and, neg_eq_self_iff]
  split_ifs with h2
  · simp only [mem_insert, mem_singleton]
    constructor
    · rintro (h | h)
      · left; exact (ZMod.val_eq_zero k).1 h
      · right
        apply ZMod.val_injective
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        omega
    · rintro (rfl | rfl)
      · left; simp
      · right
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        omega
  · simp only [mem_singleton]
    constructor
    · rintro (h | h)
      · exact (ZMod.val_eq_zero k).1 h
      · exact absurd ⟨k.val, h.symm⟩ h2
    · rintro rfl; left; simp

lemma zero_ne_half (h2 : 2 ∣ n) : (0 : ZMod n) ≠ ((n / 2 : ℕ) : ZMod n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
  omega

lemma sign_neg_zmod :
    (Equiv.Perm.sign (Equiv.neg (ZMod n)) : ℤ) = (-1) ^ ((n - if 2 ∣ n then 2 else 1) / 2) := by
  have hsq : (Equiv.neg (ZMod n)) ^ 2 = 1 := by
    ext x; simp [sq, Equiv.Perm.mul_apply]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, ZMod.card]
  have hcard : Fintype.card (Function.fixedPoints (Equiv.neg (ZMod n))) =
      (univ.filter fun k : ZMod n => -k = k).card := by
    rw [← Set.toFinset_card]
    congr 1
    ext k
    simp [Function.IsFixedPt]
  rw [hcard, fix_filter]
  split_ifs with h2
  · rw [card_pair (zero_ne_half n h2)]; push_cast; rfl
  · rw [card_singleton]; push_cast; rfl

lemma prod_mu_sign (hsq : Squarefree n) :
    ∏ k : ZMod n, μ (n / Nat.gcd k.val n) = if 2 ∣ n then -1 else 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set s := fun k : ZMod n => μ (n / Nat.gcd k.val n) with hs
  have hs_neg : ∀ k, s (-k) = s k := by
    intro k
    simp only [hs, ZMod.neg_val]
    split_ifs with hk
    · simp [hk]
    · rw [Nat.gcd_self_sub_left (ZMod.val_lt k).le]
  have hs_sq : ∀ k, s k * s k = 1 := by
    intro k
    rw [← sq]
    exact moebius_sq_eq_one_of_squarefree
      (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)))
  show ∏ k : ZMod n, s k = _
  rw [← prod_filter_mul_prod_filter_not univ (fun k => -k = k)]
  have hnon : ∏ k ∈ univ.filter (fun k : ZMod n => ¬ -k = k), s k = 1 := by
    refine prod_involution (fun a _ => -a) (fun a _ => by rw [hs_neg]; exact hs_sq a)
      (fun a ha _ => (mem_filter.1 ha).2) (fun a ha => ?_) (fun a _ => neg_neg a)
    simp only [mem_filter, mem_univ, true_and, neg_neg] at ha ⊢
    exact fun h => ha h.symm
  rw [hnon, mul_one, fix_filter]
  have hs0 : s 0 = 1 := by
    simp only [hs, ZMod.val_zero, Nat.gcd_zero_left, Nat.div_self hn, moebius_apply_one]
  split_ifs with h2
  · rw [prod_pair (zero_ne_half n h2), hs0, one_mul]
    simp only [hs, ZMod.val_natCast, Nat.mod_eq_of_lt (show n / 2 < n by omega)]
    rw [Nat.gcd_eq_left (Nat.div_dvd_of_dvd h2), Nat.div_div_self h2 hn.ne',
      moebius_apply_prime Nat.prime_two]
  · rw [prod_singleton, hs0]

end Signs

lemma tri_parity (n : ℕ) : ((-1 : ℤ)) ^ (n * (n - 1) / 2) = (-1) ^ (n / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 4 with h | h
    · interval_cases n <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h1 : (m + 4) * (m + 4 - 1) = m * (m - 1) + 2 * (4 * m + 6) := by
        rcases m with _ | j
        · norm_num
        · simp only [Nat.add_sub_cancel]
          rw [show j + 1 + 4 - 1 = j + 4 by omega]
          ring
      rw [h1, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), pow_add,
        Even.neg_one_pow (n := 4 * m + 6) ⟨2 * m + 3, by ring⟩, mul_one,
        show (m + 4) / 2 = m / 2 + 2 by omega, pow_add, Even.neg_one_pow (n := 2) ⟨1, rfl⟩,
        mul_one,
        ih m (by omega)]

/-- Product of `φ(gcd(k, n))` over `k < n` (Oudra's product). -/
lemma prod_totient_gcd (n : ℕ) (hn : 0 < n) :
    ∏ k ∈ range n, (Nat.totient (Nat.gcd k n) : ℤ) =
      ∏ d ∈ n.divisors, (Nat.totient d : ℤ) ^ Nat.totient (n / d) := by
  rw [show ∏ k ∈ range n, (Nat.totient (Nat.gcd k n) : ℤ) =
      ∏ k ∈ range n, (Nat.totient (Nat.gcd n k) : ℤ) from
    prod_congr rfl fun k _ => by rw [Nat.gcd_comm]]
  rw [← prod_fiberwise_of_maps_to' (s := range n) (t := n.divisors) (g := fun k => Nat.gcd n k)
    (fun k _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n k, hn.ne'⟩)
    (fun d => (Nat.totient d : ℤ))]
  refine prod_congr rfl fun d hd => ?_
  rw [prod_const, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]

/-- `a(n) = det [ [gcd(i + j, n) = 1] ]_{1 ≤ i, j ≤ n}` (OEIS A228885); `i, j ∈ Fin n` stand for
`i + 1, j + 1`. -/
def a228885 (n : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin n =>
    if Nat.Coprime ((i : ℕ) + 1 + ((j : ℕ) + 1)) n then (1 : ℤ) else 0).det

/-- Oudra's formula for squarefree `n`: `a(n) = (-1)^⌊n/2⌋ ∏_{d ∣ n} φ(d)^φ(n/d)`. -/
theorem A228885_formula (n : ℕ) (hn : 0 < n) (hsq : Squarefree n) :
    a228885 n = (-1) ^ (n / 2) * ∏ d ∈ n.divisors, (Nat.totient d : ℤ) ^ Nat.totient (n / d) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Integer form of the determinant.
  have hdet : a228885 (m + 1) = (Equiv.Perm.sign (Equiv.neg (ZMod (m + 1))) : ℤ) *
      ∏ k : ZMod (m + 1), ram (m + 1) k.val := by
    apply Int.cast_injective (α := ℂ)
    rw [a228885]
    change (Int.castRingHom ℂ) (Matrix.det _) = _
    rw [RingHom.map_det, ← det_reindex_self (ZMod.finEquiv (m + 1)).toEquiv]
    have hval : ∀ x : ZMod (m + 1),
        (((ZMod.finEquiv (m + 1)).toEquiv.symm x : Fin (m + 1)) : ℕ) = x.val := fun x => rfl
    have hM : reindex (ZMod.finEquiv (m + 1)).toEquiv (ZMod.finEquiv (m + 1)).toEquiv
        ((Int.castRingHom ℂ).mapMatrix (Matrix.of fun i j : Fin (m + 1) =>
          if Nat.Coprime ((i : ℕ) + 1 + ((j : ℕ) + 1)) (m + 1) then (1 : ℤ) else 0)) =
        Matrix.of fun x y : ZMod (m + 1) =>
          (fun z : ZMod (m + 1) => if Nat.Coprime z.val (m + 1) then (1 : ℂ) else 0) (x + y + 2) := by
      ext x y
      simp only [reindex_apply, submatrix_apply, RingHom.mapMatrix_apply, map_apply, of_apply]
      rw [hval, hval]
      have hc : Nat.Coprime (x.val + 1 + (y.val + 1)) (m + 1) ↔
          Nat.Coprime (x + y + 2 : ZMod (m + 1)).val (m + 1) := by
        have : (x + y + 2 : ZMod (m + 1)) = ((x.val + 1 + (y.val + 1) : ℕ) : ZMod (m + 1)) := by
          push_cast
          rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
          ring
        rw [this, ZMod.val_natCast]
        unfold Nat.Coprime
        rw [← Nat.gcd_rec, Nat.gcd_comm]
      by_cases h : Nat.Coprime (x.val + 1 + (y.val + 1)) (m + 1)
      · rw [ite_eq_left h, ite_eq_left (hc.1 h)]; simp
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hc.2 h'))]; simp
    rw [hM]
    erw [det_hankel_zmod (m + 1)
      (fun z : ZMod (m + 1) => if Nat.Coprime z.val (m + 1) then (1 : ℂ) else 0)]
    simp_rw [eig_ram]
    push_cast
    rfl
  rw [hdet]
  have hram : ∀ k : ZMod (m + 1), ram (m + 1) k.val =
      μ ((m + 1) / Nat.gcd k.val (m + 1)) * Nat.totient (Nat.gcd k.val (m + 1)) :=
    fun k => ram_squarefree (m + 1) k.val hn hsq
  rw [prod_congr rfl fun k _ => hram k, prod_mul_distrib, prod_mu_sign (m + 1) hsq,
    sign_neg_zmod]
  have hphi : ∏ k : ZMod (m + 1), (Nat.totient (Nat.gcd k.val (m + 1)) : ℤ) =
      ∏ k ∈ range (m + 1), (Nat.totient (Nat.gcd k (m + 1)) : ℤ) :=
    Fin.prod_univ_eq_prod_range (fun k => (Nat.totient (Nat.gcd k (m + 1)) : ℤ)) (m + 1)
  rw [hphi, prod_totient_gcd (m + 1) hn, ← mul_assoc]
  congr 1
  split_ifs with h2
  · rw [← pow_succ]
    congr 1
    omega
  · rw [mul_one]
    congr 1
    omega

/-- Sun's conjecture: `(-1)^(n(n-1)/2) a(n) > 0` for squarefree `n`. -/
theorem A228885_sign (n : ℕ) (hn : 0 < n) (hsq : Squarefree n) :
    0 < (-1) ^ (n * (n - 1) / 2) * a228885 n := by
  rw [A228885_formula n hn hsq, tri_parity, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]
  refine prod_pos fun d hd => pow_pos ?_ _
  exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_mem_divisors hd)
