/-
OEIS A228456, Mathlib proof: positivity of a(n) = det [A086618(i+j)]_{0 <= i,j <= n},
where A086618(n) = s(n) = Sum_{k=0..n} C(n,k)^2 C_k (C_k = Mathlib `catalan k`).

Main theorem `A228456_pos`: 0 < det [s(i+j)]_{0 <= i,j <= n} (over ℤ) for every n.

Proof. Laurent polynomials in (z, y), AddMonoidAlgebra ℝ (ℤ × ℤ). With
  w = y + 1/y,  L = (1 + w z)(1 + w/z),  W = y - 1/y,  V = W * W(1/y) = 2 - y^2 - y^-2,
* `ct_L_pow`: CT(L^n V) = 2 s(n) (the z-constant term pairs C(n,a) C(n,b) with a = b,
  and CT_y(w^(2a) V) = 2 C(2a,a) - 2 C(2a,a+1) = 2 C_a, `g_two_mul`);
* `refl_L`: L(1/z, 1/y) = L;
* the quadratic form of [s(i+j)] at c is CT(P * P(1/x)) / 2 with P = (Sum c_i L^i) W,
  the sum of the squared coefficients of P (`ct_mul_refl_pos`, using
  OpenProblemsLib.MomentHankel.ct_mul and coeff_refl_neg);
* `indep`: P = 0 forces c = 0 (evaluate at z = j+1, y = 2: W -> 3/2,
  L -> 29/4 + 5/2 (t + 1/t), injective; Vandermonde).

Checked here: a(n) > 0 for all n.
Not checked here: a(n) odd (README: reduces mod 2 to the Hankel determinants of the
period-doubling sequence, odd by Allouche-Peyriere-Wen-Wen 1998, Prop. 2.2, cited,
not formalised), and the mod-8 clause (open; checked n <= 300 in certificate/h8.py).
-/
import Mathlib
import OpenProblemsLib.MomentHankel
open Finset AddMonoidAlgebra OpenProblemsLib.MomentHankel

abbrev G2 := ℤ × ℤ

theorem ct_single (g : G2) (r : ℝ) : ct (single g r) = if g = 0 then r else 0 := by
  simp only [ct, coeff_single, Finsupp.single_apply]

theorem ct_sub (P R : AddMonoidAlgebra ℝ G2) : ct (P - R) = ct P - ct R := by
  simp [ct]

noncomputable def w : AddMonoidAlgebra ℝ G2 := single (0, 1) 1 + single (0, -1) 1
noncomputable def V : AddMonoidAlgebra ℝ G2 := single 0 2 - single (0, 2) 1 - single (0, -2) 1
noncomputable def L : AddMonoidAlgebra ℝ G2 :=
  (1 + w * single (1, 0) 1) * (1 + w * single (-1, 0) 1)

theorem w_pow (m : ℕ) :
    w ^ m = ∑ c ∈ range (m + 1), single ((0 : ℤ), 2 * (c : ℤ) - m) ((m.choose c : ℕ) : ℝ) := by
  rw [w, add_pow]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc' : c ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
  rw [single_pow, single_pow, single_mul_single, AddMonoidAlgebra.natCast_def, single_mul_single]
  congr 1
  · ext
    · simp
    · simp [Prod.smul_mk]; push_cast [Nat.cast_sub hc']; ring
  · simp

/-- the y-part constant term -/
noncomputable def g (m : ℕ) : ℝ :=
  ∑ c ∈ range (m + 1), ((m.choose c : ℕ) : ℝ) *
    ((if 2 * (c : ℤ) - m = 0 then 2 else 0) - (if 2 * (c : ℤ) - m + 2 = 0 then 1 else 0)
      - (if 2 * (c : ℤ) - m - 2 = 0 then 1 else 0))

theorem T_eq (j : ℤ) (m : ℕ) :
    ct (single (j, 0) 1 * w ^ m * V) = if j = 0 then g m else 0 := by
  rw [w_pow, V, Finset.mul_sum, Finset.sum_mul, ct_sum]
  simp only [mul_sub, single_mul_single, ct_sub, ct_single]
  split_ifs with hj
  · subst hj
    rw [g]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
    split_ifs <;> first | (exfalso; omega) | ring
  · refine Finset.sum_eq_zero fun c _ => ?_
    simp [Prod.ext_iff, hj]

theorem g_two_mul (a : ℕ) : g (2 * a) = 2 * (catalan a : ℝ) := by
  have hcat : ((a + 1 : ℕ) : ℝ) * catalan a = ((2 * a).choose a : ℝ) := by
    rw [← Nat.cast_mul, succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  have hsucc : (((2 * a).choose (a + 1) : ℕ) : ℝ) * (a + 1) = ((2 * a).choose a : ℝ) * a := by
    have := Nat.choose_succ_right_eq (2 * a) a
    have h2 : 2 * a - a = a := by omega
    rw [h2] at this
    exact_mod_cast this
  have hsym : a ≥ 1 → (2 * a).choose (a - 1) = (2 * a).choose (a + 1) := by
    intro ha
    rw [← Nat.choose_symm (by omega : a - 1 ≤ 2 * a)]
    congr 1; omega
  -- main: g(2a) = 2 C(2a,a) - 2 C(2a,a+1)
  have hg : g (2 * a) = 2 * ((2 * a).choose a : ℝ) - 2 * (((2 * a).choose (a + 1) : ℕ) : ℝ) := by
    rw [g]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ c ∈ range (2 * a + 1), (((2 * a).choose c : ℕ) : ℝ) *
        (if 2 * (c : ℤ) - ((2 * a : ℕ) : ℤ) = 0 then (2 : ℝ) else 0) = 2 * ((2 * a).choose a : ℝ) := by
      rw [Finset.sum_eq_single a]
      · split_ifs with h
        · ring
        · exfalso; push_cast at h; omega
      · intro c _ hc
        split_ifs with h
        · exfalso; push_cast at h; omega
        · ring
      · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    have e2 : ∑ c ∈ range (2 * a + 1), (((2 * a).choose c : ℕ) : ℝ) *
        (if 2 * (c : ℤ) - ((2 * a : ℕ) : ℤ) + 2 = 0 then (1 : ℝ) else 0) =
        (((2 * a).choose (a + 1) : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · rw [Finset.sum_eq_single (a - 1)]
        · split_ifs with h
          · rw [hsym ha]; ring
          · exfalso; push_cast [Nat.cast_sub ha] at h; omega
        · intro c _ hc
          split_ifs with h
          · exfalso; push_cast at h; omega
          · ring
        · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    have e3 : ∑ c ∈ range (2 * a + 1), (((2 * a).choose c : ℕ) : ℝ) *
        (if 2 * (c : ℤ) - ((2 * a : ℕ) : ℤ) - 2 = 0 then (1 : ℝ) else 0) =
        (((2 * a).choose (a + 1) : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · rw [Finset.sum_eq_single (a + 1)]
        · split_ifs with h
          · ring
          · exfalso; push_cast at h; omega
        · intro c _ hc
          split_ifs with h
          · exfalso; push_cast at h; omega
          · ring
        · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    rw [e1, e2, e3]; ring
  rw [hg]
  have ha1 : ((a : ℝ) + 1) ≠ 0 := by positivity
  have hc2 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  rw [hc2] at hcat
  field_simp
  nlinarith [hcat, hsucc]

/-- A086618(n) = Σ_k C(n,k)^2 C_k. -/
def s (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * catalan k

theorem binom_expand (n : ℕ) (e : G2) :
    (1 + w * single e 1) ^ n =
      ∑ a ∈ range (n + 1), ((n.choose a : ℕ) : ℝ) • (single (a • e) 1 * w ^ a) := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [one_pow, mul_one, mul_pow, single_pow, one_pow, mul_comm, ← nsmul_eq_mul,
    ← Nat.cast_smul_eq_nsmul ℝ, mul_comm]

theorem ct_L_pow (n : ℕ) : ct (L ^ n * V) = 2 * (s n : ℝ) := by
  rw [L, mul_pow, binom_expand, binom_expand, Finset.sum_mul_sum, Finset.sum_mul, ct_sum]
  have hterm : ∀ a b : ℕ,
      ((n.choose a : ℕ) : ℝ) • (single (a • ((1 : ℤ), (0 : ℤ))) 1 * w ^ a) *
        (((n.choose b : ℕ) : ℝ) • (single (b • ((-1 : ℤ), (0 : ℤ))) 1 * w ^ b)) * V =
      (((n.choose a : ℕ) : ℝ) * ((n.choose b : ℕ) : ℝ)) •
        (single ((a : ℤ) - b, (0 : ℤ)) 1 * w ^ (a + b) * V) := by
    intro a b
    have hs : single (a • ((1 : ℤ), (0 : ℤ))) (1 : ℝ) * single (b • ((-1 : ℤ), (0 : ℤ))) 1 =
        single ((a : ℤ) - b, (0 : ℤ)) 1 := by
      rw [single_mul_single, one_mul]
      congr 1
      ext <;> simp [Prod.smul_mk]; ring
    rw [smul_mul_smul_comm, smul_mul_assoc, mul_smul]
    rw [show single (a • ((1 : ℤ), (0 : ℤ))) (1 : ℝ) * w ^ a * (single (b • ((-1 : ℤ), (0 : ℤ))) 1 * w ^ b)
        = (single (a • ((1 : ℤ), (0 : ℤ))) (1 : ℝ) * single (b • ((-1 : ℤ), (0 : ℤ))) 1) * w ^ (a + b) by
          rw [pow_add]; ring, hs]
    rw [mul_smul]
  have key : ∀ a ∈ range (n + 1),
      ct ((∑ b ∈ range (n + 1), ((n.choose a : ℕ) : ℝ) • (single (a • ((1 : ℤ), (0 : ℤ))) 1 * w ^ a) *
        (((n.choose b : ℕ) : ℝ) • (single (b • ((-1 : ℤ), (0 : ℤ))) 1 * w ^ b))) * V) =
      2 * ((((n.choose a : ℕ) : ℝ)) ^ 2 * (catalan a : ℝ)) := by
    intro a ha
    rw [Finset.sum_mul, ct_sum]
    have hb : ∀ b ∈ range (n + 1),
        ct (((n.choose a : ℕ) : ℝ) • (single (a • ((1 : ℤ), (0 : ℤ))) 1 * w ^ a) *
          (((n.choose b : ℕ) : ℝ) • (single (b • ((-1 : ℤ), (0 : ℤ))) 1 * w ^ b)) * V) =
        ((n.choose a : ℕ) : ℝ) * ((n.choose b : ℕ) : ℝ) *
          (if (a : ℤ) - b = 0 then g (a + b) else 0) := by
      intro b _
      rw [hterm a b, ct_smul, T_eq]
    rw [Finset.sum_congr rfl hb, Finset.sum_eq_single a]
    · simp only [sub_self, ite_true, ← two_mul, g_two_mul]; ring
    · intro b _ hb'
      have : (a : ℤ) - b ≠ 0 := by omega
      simp [this]
    · intro h; exact absurd ha h
  rw [Finset.sum_congr rfl key, s]
  push_cast
  rw [Finset.mul_sum]

noncomputable def W : AddMonoidAlgebra ℝ G2 := single (0, 1) 1 - single (0, -1) 1

theorem V_eq : W * negRefl W = V := by
  have h1 : negRefl W = single (0, -1) 1 - single (0, 1) 1 := by
    simp [W, refl_single]
  rw [h1, W, V]
  have e : ∀ (x y : AddMonoidAlgebra ℝ G2), (x - y) * (y - x) = x * y + y * x - x * x - y * y := by
    intro x y; ring
  rw [e]
  simp only [single_mul_single]
  have h0 : ((0 : ℤ), (1 : ℤ)) + (0, -1) = 0 := by ext <;> simp
  have h0' : ((0 : ℤ), (-1 : ℤ)) + (0, 1) = 0 := by ext <;> simp
  have h2 : ((0 : ℤ), (1 : ℤ)) + (0, 1) = (0, 2) := by ext <;> norm_num
  have h3 : ((0 : ℤ), (-1 : ℤ)) + (0, -1) = (0, -2) := by ext <;> norm_num
  rw [h0, h0', h2, h3, ← single_add]
  norm_num

theorem refl_w : negRefl w = w := by
  simp [w, refl_single, add_comm]

theorem refl_L : negRefl L = L := by
  simp only [L, map_mul, map_add, map_one, refl_w, refl_single]
  have : (-((1 : ℤ), (0 : ℤ))) = (-1, 0) := by ext <;> simp
  have h' : (-((-1 : ℤ), (0 : ℤ))) = (1, 0) := by ext <;> simp
  rw [this, h', mul_comm]

/-- ct (P * P(1/x)) is the sum of squared coefficients, positive for P ≠ 0. -/
theorem ct_mul_refl_pos (P : AddMonoidAlgebra ℝ G2) (h0 : P ≠ 0) : 0 < ct (P * negRefl P) := by
  rw [ct_mul]
  have hsq : ∀ a ∈ P.coeff.support, P.coeff a * (negRefl P).coeff (-a) = P.coeff a ^ 2 := by
    intro a _; rw [coeff_refl_neg, sq]
  rw [Finset.sum_congr rfl hsq]
  have hne : P.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    simpa using h0
  obtain ⟨a, ha⟩ := hne
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨a, ha, by have := Finsupp.mem_support_iff.mp ha; positivity⟩

noncomputable def phi (t : ℝ) (ht : t ≠ 0) : Multiplicative G2 →* ℝ where
  toFun e := t ^ (e.toAdd.1) * (2 : ℝ) ^ (e.toAdd.2)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    rw [zpow_add₀ ht, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring

noncomputable def ev (t : ℝ) (ht : t ≠ 0) : AddMonoidAlgebra ℝ G2 →ₐ[ℝ] ℝ :=
  AddMonoidAlgebra.lift ℝ ℝ G2 (phi t ht)

theorem ev_single (t : ℝ) (ht : t ≠ 0) (x y : ℤ) :
    ev t ht (single (x, y) 1) = t ^ x * (2 : ℝ) ^ y := by
  simp [ev, phi]

theorem ev_L (t : ℝ) (ht : t ≠ 0) :
    ev t ht L = 1 + 25 / 4 + 5 / 2 * (t + t⁻¹) := by
  simp only [L, w, map_mul, map_add, map_one, ev_single]
  simp
  field_simp
  ring

theorem ev_W (t : ℝ) (ht : t ≠ 0) : ev t ht W = 3 / 2 := by
  simp only [W, map_sub, ev_single]
  norm_num

theorem v_strictMono : StrictMono fun s : ℕ => ((s : ℝ) + 1) + ((s : ℝ) + 1)⁻¹ := by
  refine strictMono_nat_of_lt_succ fun s => ?_
  have h1 : ((s : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [s.cast_nonneg (α := ℝ)])
  have h2 : 0 < (((s + 1 : ℕ) : ℝ) + 1)⁻¹ := by positivity
  push_cast at *
  linarith

theorem indep (N : ℕ) (c : Fin N → ℝ) (h : (∑ i, c i • L ^ (i : ℕ)) * W = 0) : c = 0 := by
  have ht : ∀ j : Fin N, ((j : ℕ) : ℝ) + 1 ≠ 0 := fun j => by positivity
  refine Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
    (f := fun j => 1 + 25 / 4 + 5 / 2 * ((((j : ℕ) : ℝ) + 1) + (((j : ℕ) : ℝ) + 1)⁻¹)) ?_ ?_
  · intro a b hab
    have hv : ((a : ℕ) : ℝ) + 1 + (((a : ℕ) : ℝ) + 1)⁻¹ = ((b : ℕ) : ℝ) + 1 + (((b : ℕ) : ℝ) + 1)⁻¹ := by
      simp only at hab; linarith
    exact Fin.ext (v_strictMono.injective hv)
  · intro j
    have := congrArg (ev _ (ht j)) h
    rw [map_mul, ev_W, map_zero] at this
    have h2 : ev _ (ht j) (∑ i, c i • L ^ (i : ℕ)) = 0 := by linarith
    simpa [map_sum, map_pow, ev_L] using h2

/-- **A228456, positivity.** det [A086618(i+j)]_{0 ≤ i,j ≤ n} > 0 for every n. -/
theorem A228456_pos (n : ℕ) :
    0 < (Matrix.of fun i j : Fin (n + 1) => ((s ((i : ℕ) + j) : ℕ) : ℤ)).det := by
  have hpd : (Matrix.of fun i j : Fin (n + 1) => ((s ((i : ℕ) + j) : ℕ) : ℝ)).PosDef := by
    refine ⟨Matrix.IsHermitian.ext fun i j => by simp [add_comm], fun x hx => ?_⟩
    rw [form_eq]
    set Q : AddMonoidAlgebra ℝ G2 := ∑ i, x i • L ^ (i : ℕ) with hQdef
    have hQ : negRefl Q = Q := by simp only [hQdef, map_sum, refl_smul, map_pow, refl_L]
    have hform : (∑ i, ∑ j, x i * (Matrix.of fun i j : Fin (n + 1) => ((s ((i : ℕ) + j) : ℕ) : ℝ)) i j * x j)
        = ct ((Q * W) * negRefl (Q * W)) / 2 := by
      rw [map_mul, hQ, show Q * W * (Q * negRefl W) = Q * Q * (W * negRefl W) by ring, V_eq,
        hQdef, Finset.sum_mul_sum, Finset.sum_mul, ct_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul, ct_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_smul_comm, ← pow_add, smul_mul_assoc, ct_smul, ct_L_pow]
      simp [Matrix.of_apply]
      ring
    rw [hform]
    have hP : Q * W ≠ 0 := by
      intro h0
      apply hx
      have := indep (n + 1) x (by rw [← hQdef]; exact h0)
      ext i
      simpa using congrFun this i
    have := ct_mul_refl_pos (Q * W) hP
    linarith
  have hdet := hpd.det_pos
  have hmat : (Matrix.of fun i j : Fin (n + 1) => ((s ((i : ℕ) + j) : ℕ) : ℝ)) =
      (Matrix.of fun i j : Fin (n + 1) => ((s ((i : ℕ) + j) : ℕ) : ℤ)).map (Int.castRingHom ℝ) := by
    ext i j
    simp
  rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
  exact Int.cast_pos.mp hdet
