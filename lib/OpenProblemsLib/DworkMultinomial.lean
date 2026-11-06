import Mathlib
import OpenProblemsLib.Dwork

/-!
# Frobenius congruences for multinomial coefficients, and Gauss congruences of partition sums

From `P^(p n) ≡ (expand p P)^n (mod p^(1 + v_p n))` for `P = x_0 + ... + x_(K-1)` in `ℤ[x_i]`:

* `multinomial_smul_congr`: `p^e ∣ n`, `m.sum = n` ⇒
  `p^(e+1) ∣ multinomial (p • m) - multinomial m` (multisets of naturals).
* `multinomial_dvd_of_not_dvd`: `p^e ∣ n`, `m.sum = p n`, some element not divisible by `p` ⇒
  `p^(e+1) ∣ multinomial m`.
* `multinomial_mul_prod_factorial`: `multinomial m * ∏ x! = (∑ x)!`.
* `partitionSum r n = ∑_{λ ⊢ n} multinomial(λ)^r` (`r ≥ 1`) satisfies the Gauss congruences at
  every prime (`LGp_partitionSum`); hence `exp (∑ partitionSum r n x^n / n)` is an integer series.
  This replaces the necklace-action argument of OEIS/A183241/README.md, item 1.
-/

namespace OpenProblemsLib.DworkMultinomial

open MvPolynomial OpenProblemsLib.Dwork

/-- `x_0 + ... + x_(K-1)`. -/
noncomputable def sumX (K : ℕ) : MvPolynomial ℕ ℤ :=
  (∑ i ∈ Finset.range K, Finsupp.single i (1 : ℤ)).linearCombination ℤ X

theorem frobMv_mod (p : ℕ) (hp : p.Prime) (P : MvPolynomial ℕ ℤ) :
    (p : MvPolynomial ℕ ℤ) ∣ P ^ p - expand p P := by
  have := Fact.mk hp
  rw [← map_natCast (C : ℤ →+* MvPolynomial ℕ ℤ), C_dvd_iff_zmod, map_sub, map_pow, map_expand,
    ← frobenius_zmod, frobenius_def, sub_self]

theorem frobMv_pow_congr (p : ℕ) (hp : p.Prime) (P : MvPolynomial ℕ ℤ) (e k : ℕ)
    (hk : p ^ e ∣ k) :
    (p : MvPolynomial ℕ ℤ) ^ (e + 1) ∣ P ^ (p * k) - expand p (P ^ k) := by
  obtain ⟨t, rfl⟩ := hk
  have h1 := dvd_sub_pow_of_dvd_sub (frobMv_mod p hp P) e
  have h2 := h1.trans (sub_dvd_pow_sub_pow _ _ t)
  have e1 : P ^ (p * (p ^ e * t)) = ((P ^ p) ^ p ^ e) ^ t := by rw [← pow_mul, ← pow_mul]
  have e2 : expand p (P ^ (p ^ e * t)) = (expand p P ^ p ^ e) ^ t := by
    rw [map_pow, ← pow_mul]
  rw [e1, e2]; exact h2

theorem coeff_dvd_of_dvd (p r : ℕ) (G : MvPolynomial ℕ ℤ)
    (h : (p : MvPolynomial ℕ ℤ) ^ r ∣ G) (s : ℕ →₀ ℕ) : (p : ℤ) ^ r ∣ G.coeff s := by
  obtain ⟨H, rfl⟩ := h
  rw [← map_natCast (C : ℤ →+* MvPolynomial ℕ ℤ), ← map_pow, coeff_C_mul]
  exact dvd_mul_right _ _

theorem coeff_sumX_pow (K n : ℕ) (s : ℕ →₀ ℕ) (hs : s.support ⊆ Finset.range K)
    (hsum : (s.sum fun _ m => m) = n) : ((sumX K) ^ n).coeff s = (s.multinomial : ℤ) := by
  rw [sumX, coeff_linearCombination_X_pow]
  simp only [hsum, ↓reduceIte]
  have : (s.prod fun r m => (∑ i ∈ Finset.range K, Finsupp.single i (1 : ℤ)) r ^ m) = 1 := by
    apply Finset.prod_eq_one
    intro r hr
    have hrK := Finset.mem_range.mp (hs hr)
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hrK]
  rw [this, mul_one]

/-- Finsupp form of the congruence `multinomial (p s) ≡ multinomial s`. -/
theorem fs_smul_congr (p : ℕ) (hp : p.Prime) (K n e : ℕ) (s : ℕ →₀ ℕ)
    (hs : s.support ⊆ Finset.range K) (hsum : (s.sum fun _ m => m) = n) (hn : p ^ e ∣ n) :
    (p : ℤ) ^ (e + 1) ∣ ((p • s).multinomial : ℤ) - (s.multinomial : ℤ) := by
  have h := coeff_dvd_of_dvd p _ _ (frobMv_pow_congr p hp (sumX K) e n hn) (p • s)
  have hs' : (p • s).support ⊆ Finset.range K := (Finsupp.support_smul).trans hs
  have hsum' : ((p • s).sum fun _ m => m) = p * n := by
    rw [← hsum, Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
  rwa [coeff_sub, coeff_sumX_pow K _ _ hs' hsum', coeff_expand_smul _ hp.ne_zero,
    coeff_sumX_pow K n s hs hsum] at h

theorem fs_dvd_of_not_dvd (p : ℕ) (hp : p.Prime) (K n e : ℕ) (s : ℕ →₀ ℕ)
    (hs : s.support ⊆ Finset.range K) (hsum : (s.sum fun _ m => m) = p * n) (hn : p ^ e ∣ n)
    (i : ℕ) (hi : ¬ p ∣ s i) : (p : ℤ) ^ (e + 1) ∣ (s.multinomial : ℤ) := by
  have h := coeff_dvd_of_dvd p _ _ (frobMv_pow_congr p hp (sumX K) e n hn) s
  rwa [coeff_sub, coeff_sumX_pow K _ _ hs hsum, coeff_expand_of_not_dvd _ hi, sub_zero] at h

/-! ## Lists and multisets -/

theorem toFinsupp_support_subset (l : List ℕ) : l.toFinsupp.support ⊆ Finset.range l.length := by
  intro i hi
  rw [Finsupp.mem_support_iff, List.toFinsupp_apply] at hi
  rw [Finset.mem_range]
  by_contra h
  exact hi (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by omega : l.length ≤ i)])

theorem toFinsupp_sum' (l : List ℕ) : (l.toFinsupp.sum fun _ m => m) = l.sum := by
  have := List.toFinsupp_sum l
  simpa using this

theorem toFinsupp_map_mul (p : ℕ) (l : List ℕ) :
    (l.map (fun x => p * x)).toFinsupp = p • l.toFinsupp := by
  ext i
  simp only [List.toFinsupp_apply, Finsupp.smul_apply, smul_eq_mul, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases l[i]? <;> simp

theorem list_multinomial_smul_congr (p : ℕ) (hp : p.Prime) (e : ℕ) (l : List ℕ)
    (hn : p ^ e ∣ l.sum) :
    (p : ℤ) ^ (e + 1) ∣ ((l.map (fun x => p * x)).multinomial : ℤ) - (l.multinomial : ℤ) := by
  simp only [List.multinomial]
  rw [toFinsupp_map_mul]
  exact fs_smul_congr p hp l.length l.sum e _ (toFinsupp_support_subset l) (toFinsupp_sum' l) hn

theorem list_multinomial_dvd (p : ℕ) (hp : p.Prime) (e n : ℕ) (l : List ℕ) (hsum : l.sum = p * n)
    (hn : p ^ e ∣ n) (x : ℕ) (hx : x ∈ l) (hpx : ¬ p ∣ x) :
    (p : ℤ) ^ (e + 1) ∣ (l.multinomial : ℤ) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  apply fs_dvd_of_not_dvd p hp l.length n e _ (toFinsupp_support_subset l)
    ((toFinsupp_sum' l).trans hsum) hn i
  simpa [List.toFinsupp_apply, List.getD_eq_getElem?_getD, hi] using hpx

theorem multinomial_smul_congr (p : ℕ) (hp : p.Prime) (e : ℕ) (m : Multiset ℕ)
    (hn : p ^ e ∣ m.sum) :
    (p : ℤ) ^ (e + 1) ∣ ((m.map (fun x => p * x)).multinomial : ℤ) - (m.multinomial : ℤ) := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep m
  exact list_multinomial_smul_congr p hp e l (by simpa using hn)

theorem multinomial_dvd_of_not_dvd (p : ℕ) (hp : p.Prime) (e n : ℕ) (m : Multiset ℕ)
    (hsum : m.sum = p * n) (hn : p ^ e ∣ n) (x : ℕ) (hx : x ∈ m) (hpx : ¬ p ∣ x) :
    (p : ℤ) ^ (e + 1) ∣ (m.multinomial : ℤ) := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep m
  exact list_multinomial_dvd p hp e n l (by simpa using hsum) hn x (by simpa using hx) hpx

theorem multinomial_mul_prod_factorial (m : Multiset ℕ) :
    m.multinomial * (m.map Nat.factorial).prod = m.sum.factorial := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    rw [Multiset.multinomial_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right x m.sum)
    rw [Nat.add_sub_cancel_left] at h
    calc (x + m.sum).choose x * m.multinomial * (x.factorial * (m.map Nat.factorial).prod)
        = (x + m.sum).choose x * x.factorial * (m.multinomial * (m.map Nat.factorial).prod) := by
          ring
      _ = _ := by rw [ih, h]

/-- `multinomial λ = n! / ∏ λ_i!`. -/
theorem multinomial_eq_div (m : Multiset ℕ) :
    m.multinomial = m.sum.factorial / (m.map Nat.factorial).prod := by
  have hpos : 0 < (m.map Nat.factorial).prod :=
    Multiset.prod_pos (fun x hx => by
      obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact Nat.factorial_pos y)
  rw [← multinomial_mul_prod_factorial m, Nat.mul_div_cancel _ hpos]

/-! ## Partition sums -/

/-- `∑_{λ ⊢ n} (n! / ∏ λ_i!)^r`. -/
def partitionSum (r n : ℕ) : ℤ :=
  ∑ q : n.Partition, ((n.factorial / (q.parts.map Nat.factorial).prod : ℕ) : ℤ) ^ r

theorem partitionSum_eq (r n : ℕ) :
    partitionSum r n = ∑ q : n.Partition, ((q.parts.multinomial : ℕ) : ℤ) ^ r := by
  apply Finset.sum_congr rfl
  intro q _
  rw [multinomial_eq_div, q.parts_sum]

/-- Scale a partition of `n` by `p`. -/
def scale (p : ℕ) (hp : 0 < p) {n : ℕ} (q : n.Partition) : (p * n).Partition where
  parts := q.parts.map (fun x => p * x)
  parts_pos := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hi
    exact Nat.mul_pos hp (q.parts_pos hx)
  parts_sum := by rw [Multiset.sum_map_mul_left, Multiset.map_id', q.parts_sum]

/-- Divide a partition of `p n` with all parts divisible by `p`. -/
def unscale (p : ℕ) (hp : 0 < p) {n : ℕ} (q : (p * n).Partition) (h : ∀ x ∈ q.parts, p ∣ x) :
    n.Partition where
  parts := q.parts.map (fun x => x / p)
  parts_pos := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hi
    exact Nat.div_pos (Nat.le_of_dvd (q.parts_pos hx) (h x hx)) hp
  parts_sum := by
    have hs : p * (q.parts.map (fun x => x / p)).sum = q.parts.sum := by
      rw [← Multiset.sum_map_mul_left]
      conv_rhs => rw [← Multiset.map_id q.parts]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro x hx
      exact Nat.mul_div_cancel' (h x hx)
    rw [q.parts_sum] at hs
    exact Nat.eq_of_mul_eq_mul_left hp hs

theorem LGp_partitionSum (r : ℕ) (hr : 1 ≤ r) (p : ℕ) (hp : p.Prime) : LGp p (partitionSum r) := by
  intro a m0 ha
  have hp0 := hp.pos
  set M := m0 * p ^ (a - 1)
  have hN : m0 * p ^ a = p * M := by
    simp only [M]; rw [← mul_assoc, mul_comm p m0, mul_assoc, ← pow_succ', Nat.sub_add_cancel ha]
  have hM : p ^ (a - 1) ∣ M := Dvd.intro_left _ rfl
  rw [hN, partitionSum_eq, partitionSum_eq]
  set D : Finset (p * M).Partition := Finset.univ.filter (fun q => ∀ x ∈ q.parts, p ∣ x)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun q : (p * M).Partition =>
    ∀ x ∈ q.parts, p ∣ x)]
  have hbij : ∑ q ∈ D, ((q.parts.multinomial : ℕ) : ℤ) ^ r =
      ∑ q : M.Partition, (((q.parts.map (fun x => p * x)).multinomial : ℕ) : ℤ) ^ r := by
    symm
    apply Finset.sum_nbij' (fun q => scale p hp0 q)
      (fun q => if h : ∀ x ∈ q.parts, p ∣ x then unscale p hp0 q h else default)
    · intro q _
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, scale]
      intro x hx
      obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
      exact dvd_mul_right p y
    · intro q _; exact Finset.mem_univ _
    · intro q _
      have h : ∀ x ∈ (scale p hp0 q).parts, p ∣ x := by
        intro x hx
        obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
        exact dvd_mul_right p y
      split_ifs
      apply Nat.Partition.ext
      change Multiset.map (fun x => x / p) (Multiset.map (fun x => p * x) q.parts) = q.parts
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id q.parts]
      apply Multiset.map_congr rfl
      intro x _
      exact Nat.mul_div_cancel_left x hp0
    · intro q hq
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      split_ifs
      apply Nat.Partition.ext
      change Multiset.map (fun x => p * x) (Multiset.map (fun x => x / p) q.parts) = q.parts
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id q.parts]
      apply Multiset.map_congr rfl
      intro x hx
      exact Nat.mul_div_cancel' (hq x hx)
    · intro q _; rfl
  rw [hbij]
  have e : ∀ (A B C : ℤ), A + B - C = (A - C) + B := fun A B C => by ring
  rw [e, ← Finset.sum_sub_distrib]
  apply dvd_add
  · apply Finset.dvd_sum
    intro q _
    have h := multinomial_smul_congr p hp (a - 1) q.parts (by rw [q.parts_sum]; exact hM)
    rw [show a - 1 + 1 = a by omega] at h
    exact h.trans (sub_dvd_pow_sub_pow _ _ r)
  · apply Finset.dvd_sum
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hq
    obtain ⟨x, hx, hpx⟩ := hq
    have h := multinomial_dvd_of_not_dvd p hp (a - 1) M q.parts q.parts_sum hM x hx hpx
    rw [show a - 1 + 1 = a by omega] at h
    exact h.trans (dvd_pow_self _ (by omega))

/-- `exp (∑ partitionSum r n x^n / n)` is an integer series (`r ≥ 1`). -/
theorem expCoeff_partitionSum_int (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    ∃ z : ℤ, expCoeff (partitionSum r) n = z :=
  expCoeff_int_of_gauss _ (fun p hp => LGp_partitionSum r hr p hp) n

end OpenProblemsLib.DworkMultinomial
