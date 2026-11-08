import Mathlib

/-!
# OEIS A228884: det [gcd(i - j, n)]_{0 ≤ i, j ≤ n-1} (Sun's conjecture)

`a228884 n` is the determinant of the `n × n` integer matrix `gcd(i - j, n)`, `0 ≤ i, j < n`.

Proved here:
* `det_circulant_zmod`: a complex circulant matrix indexed by `ZMod n` has determinant
  `∏_k ∑_m v m · e(-m k)` (DFT eigenvalues, built here from `ZMod.stdAddChar`).
* `A228884_eq_prod`: `a(n) = ∏_{k < n} λ(n, k)`, `λ(n, k) = ∑_{d ∣ n, (n/d) ∣ k} φ(d) · n/d`.
* `A228884_pos`, `A228884_dvd`: part (i), `a(n) > 0` and `φ(n)^φ(n) · ∑_{d ∣ n} φ(d) n/d ∣ a(n)`
  for `n ≥ 1`.
* `A228884_ii`: part (ii), every prime factor of `a(n)` is `< n` for composite `n`.

Outside Lean: none (reading the OEIS definition as `a228884` is the only step not checked).
-/

open Finset Matrix

section Circulant

variable (n : ℕ) [NeZero n]

/-- Circulant determinant over `ZMod n` as a product of DFT eigenvalues. -/
theorem det_circulant_zmod (v : ZMod n → ℂ) :
    (circulant v).det = ∏ k : ZMod n, ∑ m : ZMod n, v m * ZMod.stdAddChar (-(m * k)) := by
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
  have hCF : circulant v * F = F * diagonal (fun k => ∑ m, v m * e (-(m * k))) := by
    ext i k
    rw [mul_diagonal]
    simp only [F, mul_apply, circulant_apply, of_apply]
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.subLeft i) _ _ (fun j => ?_)
    simp only [Equiv.subLeft_apply]
    rw [mul_left_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have := congrArg det hCF
  rw [det_mul, det_mul, det_diagonal, mul_comm (det (circulant v))] at this
  exact mul_left_cancel₀ hFdet this

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


/-- The eigenvalue `λ(n, k) = ∑_{d ∣ n, (n/d) ∣ k} φ(d) · n/d`. -/
def lam (n k : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if (n / d) ∣ k then Nat.totient d * (n / d) else 0

/-- DFT eigenvalue of the circulant `gcd(m, n)`. -/
lemma eig_gcd (k : ZMod n) :
    ∑ m : ZMod n, ((Nat.gcd m.val n : ℕ) : ℂ) * ZMod.stdAddChar (-(m * k)) = (lam n k.val : ℂ) := by
  have hn : n ≠ 0 := NeZero.ne n
  have hg : ∀ m : ZMod n, ((Nat.gcd m.val n : ℕ) : ℂ) =
      ∑ d ∈ n.divisors, if d ∣ m.val then (Nat.totient d : ℂ) else 0 := by
    intro m
    have hdiv : (Nat.gcd m.val n).divisors = n.divisors.filter (· ∣ m.val) := by
      ext d
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      have : Nat.gcd m.val n ≠ 0 := Nat.gcd_ne_zero_right hn
      tauto
    rw [← Nat.sum_totient (Nat.gcd m.val n), hdiv, sum_filter]
    push_cast
    rfl
  simp_rw [hg, sum_mul]
  rw [sum_comm]
  unfold lam
  push_cast
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have : ∀ m : ZMod n, (if d ∣ m.val then (Nat.totient d : ℂ) else 0) * ZMod.stdAddChar (-(m * k)) =
      (Nat.totient d : ℂ) * (if d ∣ m.val then ZMod.stdAddChar (-(m * k)) else 0) := by
    intro m; split_ifs <;> simp
  rw [sum_congr rfl fun m _ => this m, ← mul_sum, charsum_dvd n hdn k]
  split_ifs <;> simp

end Circulant

/-- `a(n) = det [gcd(i - j, n)]_{0 ≤ i, j ≤ n - 1}` (OEIS A228884). -/
def a228884 (n : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin n => ((Int.gcd ((i : ℤ) - (j : ℤ)) (n : ℤ) : ℕ) : ℤ)).det

/-- `a(n)` is the product of the circulant eigenvalues. -/
theorem A228884_eq_prod (n : ℕ) (hn : 0 < n) : a228884 n = ∏ k ∈ range n, (lam n k : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  apply Int.cast_injective (α := ℂ)
  rw [a228884]
  change (Int.castRingHom ℂ) (Matrix.det _) = _
  rw [RingHom.map_det]
  rw [← det_reindex_self (ZMod.finEquiv (m + 1)).toEquiv]
  have hval : ∀ x : ZMod (m + 1), ((((ZMod.finEquiv (m + 1)).toEquiv.symm x : Fin (m + 1)) : ℕ) : ℤ) =
      (x.val : ℤ) := fun x => rfl
  have hM : reindex (ZMod.finEquiv (m + 1)).toEquiv (ZMod.finEquiv (m + 1)).toEquiv
      ((Int.castRingHom ℂ).mapMatrix
        (Matrix.of fun i j : Fin (m + 1) =>
          ((Int.gcd ((i : ℤ) - (j : ℤ)) ((m + 1 : ℕ) : ℤ) : ℕ) : ℤ))) =
      circulant (fun x : ZMod (m + 1) => ((Nat.gcd x.val (m + 1) : ℕ) : ℂ)) := by
    ext x y
    simp only [reindex_apply, submatrix_apply, RingHom.mapMatrix_apply, map_apply, of_apply,
      circulant_apply, eq_intCast, Int.cast_natCast]
    rw [hval, hval]
    congr 1
    have h1 : x - y = (((x.val : ℤ) - (y.val : ℤ) : ℤ) : ZMod (m + 1)) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [h1, ← Int.gcd_natCast_natCast, ZMod.val_intCast, Int.gcd_emod]
  rw [hM, det_circulant_zmod]
  simp_rw [eig_gcd]
  push_cast
  exact Fin.prod_univ_eq_prod_range (fun k => (lam (m + 1) k : ℂ)) (m + 1)

/-- Sun's conjecture (i), positivity: `a(n) > 0`. -/
theorem A228884_pos (n : ℕ) (hn : 0 < n) : 0 < a228884 n := by
  rw [A228884_eq_prod n hn]
  refine prod_pos fun k _ => ?_
  have : 0 < lam n k := by
    unfold lam
    refine lt_of_lt_of_le ?_ (single_le_sum (fun d _ => Nat.zero_le _)
      (Nat.mem_divisors_self n hn.ne'))
    rw [Nat.div_self hn, ite_eq_left (one_dvd k), mul_one]
    exact Nat.totient_pos.2 hn
  exact_mod_cast this

lemma lam_zero (n : ℕ) : lam n 0 = ∑ d ∈ n.divisors, Nat.totient d * (n / d) := by
  unfold lam
  exact sum_congr rfl fun d _ => by rw [ite_eq_left (dvd_zero _)]

lemma lam_coprime (n k : ℕ) (hn : 0 < n) (hk : Nat.Coprime k n) : lam n k = Nat.totient n := by
  unfold lam
  rw [sum_eq_single n]
  · rw [Nat.div_self hn, ite_eq_left (one_dvd k), mul_one]
  · intro d hd hdn
    rw [ite_eq_right]
    intro hdk
    have h1 : n / d ∣ Nat.gcd k n := Nat.dvd_gcd hdk (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    rw [hk, Nat.dvd_one] at h1
    apply hdn
    have := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    rw [h1, one_mul] at this
    exact this
  · intro h; exact absurd (Nat.mem_divisors_self n hn.ne') h

/-- Sun's conjecture (i), divisibility: `φ(n)^φ(n) · ∑_{d ∣ n} φ(d) n/d` divides `a(n)`. -/
theorem A228884_dvd (n : ℕ) (hn : 0 < n) :
    ((Nat.totient n : ℤ) ^ Nat.totient n * ∑ d ∈ n.divisors, (Nat.totient d * (n / d) : ℕ)) ∣
      a228884 n := by
  rw [A228884_eq_prod n hn]
  by_cases h1 : n = 1
  · subst h1; simp
  have hcard : ((range n).filter (fun k => Nat.Coprime k n)).card = Nat.totient n := by
    rw [Nat.totient]
    congr 1
    ext k
    simp [Nat.coprime_comm]
  rw [← prod_filter_mul_prod_filter_not (range n) (fun k => Nat.Coprime k n)]
  have hcop : ∏ k ∈ (range n).filter (fun k => Nat.Coprime k n), (lam n k : ℤ) =
      (Nat.totient n : ℤ) ^ Nat.totient n := by
    rw [prod_congr rfl fun k hk => by rw [lam_coprime n k hn (mem_filter.1 hk).2], prod_const,
      hcard]
  rw [hcop]
  refine mul_dvd_mul_left _ ?_
  have h0 : 0 ∈ (range n).filter (fun k => ¬ Nat.Coprime k n) := by
    simp only [mem_filter, mem_range, Nat.coprime_zero_left]
    exact ⟨hn, h1⟩
  have := dvd_prod_of_mem (fun k => (lam n k : ℤ)) h0
  simp only [lam_zero] at this
  push_cast at this ⊢
  exact this

/-! Part (ii). `λ(n, k) = L(n, gcd(k, n))` with `L(n, g) = ∑_{e ∣ g} e φ(n/e)`, multiplicative in
`(n, g)`; the local factors at `p^a ∥ n` have only prime factors `< n` when `n` is composite. -/

/-- `L(n, g) = ∑_{e ∣ g} e · φ(n / e)`. -/
def lamL (n g : ℕ) : ℕ :=
  ∑ e ∈ g.divisors, e * Nat.totient (n / e)

lemma divisors_gcd (k n : ℕ) (hn : n ≠ 0) :
    (Nat.gcd k n).divisors = n.divisors.filter (· ∣ k) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
  have : Nat.gcd k n ≠ 0 := Nat.gcd_ne_zero_right hn
  tauto

lemma lam_eq_L (n k : ℕ) (hn : 0 < n) : lam n k = lamL n (Nat.gcd k n) := by
  unfold lam lamL
  rw [← Nat.sum_div_divisors n, divisors_gcd k n hn.ne', sum_filter]
  refine sum_congr rfl fun e he => ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hn.ne', mul_comm]

lemma lamL_mul {n₁ n₂ g₁ g₂ : ℕ} (h : Nat.Coprime n₁ n₂) (hg₁ : g₁ ∣ n₁) (hg₂ : g₂ ∣ n₂) :
    lamL (n₁ * n₂) (g₁ * g₂) = lamL n₁ g₁ * lamL n₂ g₂ := by
  have hg : Nat.Coprime g₁ g₂ := (h.coprime_dvd_left hg₁).coprime_dvd_right hg₂
  unfold lamL
  rw [Nat.divisors_mul, Finset.mul_def, sum_image hg.mul_injOn_divisors, sum_product,
    sum_mul_sum]
  refine sum_congr rfl fun e₁ he₁ => sum_congr rfl fun e₂ he₂ => ?_
  have h1 : e₁ ∣ n₁ := (Nat.dvd_of_mem_divisors he₁).trans hg₁
  have h2 : e₂ ∣ n₂ := (Nat.dvd_of_mem_divisors he₂).trans hg₂
  rw [← Nat.div_mul_div_comm h1 h2,
    Nat.totient_mul ((h.coprime_dvd_left (Nat.div_dvd_of_dvd h1)).coprime_dvd_right
      (Nat.div_dvd_of_dvd h2))]
  ring

lemma lamL_prime_pow_lt {p a b : ℕ} (hp : p.Prime) (hb : b < a) :
    lamL (p ^ a) (p ^ b) = (b + 1) * (p ^ (a - 1) * (p - 1)) := by
  unfold lamL
  rw [Nat.sum_divisors_prime_pow hp]
  rw [sum_congr rfl fun c hc => by
    rw [Nat.pow_div (by have := mem_range.1 hc; omega) hp.pos,
      Nat.totient_prime_pow hp (by have := mem_range.1 hc; omega), ← mul_assoc, ← pow_add,
      show c + (a - c - 1) = a - 1 by have := mem_range.1 hc; omega]]
  rw [sum_const, card_range, smul_eq_mul]

lemma lamL_prime_pow_self {p a : ℕ} (hp : p.Prime) :
    lamL (p ^ a) (p ^ a) = a * (p ^ (a - 1) * (p - 1)) + p ^ a := by
  unfold lamL
  rw [Nat.sum_divisors_prime_pow hp, sum_range_succ, Nat.div_self (pow_pos hp.pos a),
    Nat.totient_one, mul_one]
  congr 1
  rw [sum_congr rfl fun c hc => by
    rw [Nat.pow_div (by have := mem_range.1 hc; omega) hp.pos,
      Nat.totient_prime_pow hp (by have := mem_range.1 hc; omega), ← mul_assoc, ← pow_add,
      show c + (a - c - 1) = a - 1 by have := mem_range.1 hc; omega]]
  rw [sum_const, card_range, smul_eq_mul]

lemma local_le {p a : ℕ} (hp : 2 ≤ p) (ha : 2 ≤ a) : a * (p - 1) + p ≤ p ^ a := by
  induction a, ha using Nat.le_induction with
  | base =>
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 2 := ⟨p - 2, by omega⟩
    rw [show r + 2 - 1 = r + 1 by omega]
    nlinarith
  | succ a ha ih =>
    have hpa : 1 ≤ p ^ a := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    have : (a + 1) * (p - 1) + p = a * (p - 1) + p + (p - 1) := by ring
    rw [this]
    have h3 : p - 1 ≤ p ^ a * (p - 1) := Nat.le_mul_of_pos_left _ hpa
    have h4 : p ^ a * p = p ^ a + p ^ a * (p - 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      simp; ring
    omega

/-- Prime factors of the local factor `L(p^a, p^b)`. -/
lemma prime_dvd_L_prime_pow {p a b q : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : b ≤ a)
    (hq : q.Prime) (hdvd : q ∣ lamL (p ^ a) (p ^ b)) : q < p ^ a ∨ (a = 1 ∧ q < 2 * p) := by
  have hp2 := hp.two_le
  have hpow : ∀ c, 1 ≤ c → q ∣ p ^ c → q = p := fun c _ h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
  have hqp : q ∣ p ^ (a - 1) → 2 ≤ a ∧ q = p := by
    intro h
    by_cases ha1 : a = 1
    · subst ha1; simp at h; exact absurd h hq.ne_one
    · exact ⟨by omega, hpow (a - 1) (by omega) h⟩
  have hlt_pow : 2 ≤ a → p < p ^ a := fun h2 =>
    lt_of_lt_of_le (by simpa using Nat.pow_lt_pow_right hp2 (show 1 < 2 by norm_num))
      (Nat.pow_le_pow_right hp.pos h2)
  have hpm1 : q ∣ p - 1 → q < p ^ a := fun h => by
    have := Nat.le_of_dvd (by omega) h
    have : p ≤ p ^ a := Nat.le_self_pow ha.ne' p
    omega
  rcases Nat.lt_or_eq_of_le hb with hb | hb
  · rw [lamL_prime_pow_lt hp hb] at hdvd
    left
    rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
    · have h1 := Nat.le_of_dvd (by omega) h
      have : a < 2 ^ a := Nat.lt_two_pow_self
      have : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp2 a
      omega
    · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
      · obtain ⟨h2, rfl⟩ := hqp h; exact hlt_pow h2
      · exact hpm1 h
  · subst hb
    rw [lamL_prime_pow_self hp] at hdvd
    have hfac : b * (p ^ (b - 1) * (p - 1)) + p ^ b = p ^ (b - 1) * (b * (p - 1) + p) := by
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
    rw [hfac] at hdvd
    rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
    · obtain ⟨h2, rfl⟩ := hqp h; left; exact hlt_pow h2
    · have h1 := Nat.le_of_dvd (by positivity) h
      by_cases hb1 : b = 1
      · subst hb1; right; refine ⟨rfl, ?_⟩; omega
      · left
        have hle := local_le hp2 (show 2 ≤ b by omega)
        rcases Nat.lt_or_eq_of_le (h1.trans hle) with hlt | heq
        · exact hlt
        · exfalso
          rw [heq] at hq
          exact (Nat.Prime.pow_eq_iff hq).1 rfl |>.2 |> (fun h => hb1 h)

/-- Prime factors of `L(n, g)`: below `n`, or below `2n` when `n` is prime. -/
lemma prime_dvd_lamL (n : ℕ) : 0 < n → ∀ g, g ∣ n → ∀ q, q.Prime → q ∣ lamL n g →
    q < n ∨ (n.Prime ∧ q < 2 * n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ g hg q hq hdvd
    rw [Nat.dvd_one.1 hg] at hdvd
    simp [lamL] at hdvd
    exact absurd hdvd hq.ne_one
  | prime_pow p a hp ha =>
    intro _ g hg q hq hdvd
    obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow hp).1 hg
    rcases prime_dvd_L_prime_pow hp ha hb hq hdvd with h | ⟨rfl, h⟩
    · exact Or.inl h
    · right; rw [pow_one]; exact ⟨hp, h⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ g hg q hq hdvd
    have hge : g = Nat.gcd g a * Nat.gcd g b := by
      rw [← Nat.Coprime.gcd_mul g hab, Nat.gcd_eq_left hg]
    rw [hge, lamL_mul hab (Nat.gcd_dvd_right g a) (Nat.gcd_dvd_right g b)] at hdvd
    left
    rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
    · rcases iha (by omega) _ (Nat.gcd_dvd_right g a) q hq h with h' | ⟨_, h'⟩
      · nlinarith
      · nlinarith
    · rcases ihb (by omega) _ (Nat.gcd_dvd_right g b) q hq h with h' | ⟨_, h'⟩
      · nlinarith
      · nlinarith

/-- Sun's conjecture (ii): for composite `n`, every prime factor of `a(n)` is below `n`. -/
theorem A228884_ii (n : ℕ) (hn : 1 < n) (hnp : ¬ n.Prime) (p : ℕ) (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ a228884 n) : p < n := by
  rw [A228884_eq_prod n (by omega)] at hdvd
  have : (p : ℤ) ∣ ((∏ k ∈ range n, lam n k : ℕ) : ℤ) := by push_cast; exact hdvd
  rw [Int.natCast_dvd_natCast] at this
  obtain ⟨k, _, hk⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 this
  rw [lam_eq_L n k (by omega)] at hk
  rcases prime_dvd_lamL n (by omega) _ (Nat.gcd_dvd_right k n) p hp hk with h | ⟨h, _⟩
  · exact h
  · exact absurd h hnp
