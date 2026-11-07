import Mathlib
import OpenProblemsLib.AutomaticMod

/-!
# Hanna's series A183161, A219197 modulo 4: a six-state automaton

Let `G = 1 + x G³` (ternary trees, A001764) and let `A` be the power series with `A(0) = 1` and
`A² (1 - 2x G² - 3x² G⁴) = 1`; by Hanna's formulas in the OEIS entries, `A` is the g.f. of
A183161 and `G A` that of A219197. This module proves that no coefficient of `A` or of `G A` is
`3 (mod 4)` (`gf_mod4`), i.e. the conjectures in A183161, A218622 and A219197.

Proof.
* Lagrange inversion for `x = t (1 - t)²` (`lagrange`): `[xⁿ] F = [tⁿ] F(t(1-t)²)(1-3t)(1-t)^(-2n-1)`,
  proved by splitting `F` into its first `n + 1` monomials and a multiple of `x^(n+1)`, using
  `[t^d] (1-3t)(1-t)^(-2d-1) = [d = 0]` (`coeff_kernel`, from `C(3d,d) = 3 C(3d-1,d-1)`).
  Under the substitution `G ↦ 1/(1-t)` (`ψ_G`, uniqueness of the root of `g = 1 + u g³`) and
  `x G² ↦ t`, so `[xⁿ] G^c A = [tⁿ] S(t) (1-t)^(-2n-1-c)` with `S = ψ(A)(1-3t)`,
  `S(0) = 1`, `S² (1 + t) = 1 - 3t`.
* `S ≡ 1 + 2W (mod 4)` (`S_mod4`), where `W = ∑ {tᵐ : m ≥ 1, v₂(m) even}`: modulo 2,
  `S ≡ 1`; writing `S = 1 + 2E` gives `(E + E²)(1 + t) = -t` exactly, and `W` satisfies
  `(1 - t)(W + W(t²)) = t` (`WZ_add_expand`) and `W² = W(t²)` modulo 2, so `E ≡ W (mod 2)`.
* `[tⁿ] (1 + 2W)(1-t)^(-2n-1-c) = diag F (n)` with `F = (1-t)^(2-c) Q (1 + 2W) / Q²`,
  `Q = (1-t)((1-t)² - x)` over `ℤ/4` (`val_init`).
* `AutomaticMod.ry_step` with basis `(1, W)`, `U = M = Q²` (`Q⁴ = Q(x², t²)²` checked by
  `decide`, `frob_ok`) and `Q² W = t(1-t)B² · 1 - Q² · W(t²)` (`he`): the Cartier step maps the
  numerator pairs of six explicit states `st` among themselves (`step_ok`, by `decide`), and
  the constant terms of the six states are `1, 1, 2, 2, 2, 0` (`out_ok`).

* From the definitions (`conv_root_mod4`): Hanna's g.f. formula is not assumed. By `lagrange`
  and the Fibonacci-polynomial identity `(1 + t) ∑_k C(N-k, k) tᵏ (1-t)^(N-2k) = 1 - (-t)^(N+1)`
  (`fibT_closed`), A183160(n) = [tⁿ] (1+t)⁻¹ (1-t)^(-2n-1) and A199033(n) = [tⁿ] (1+t)⁻¹ (1-t)^(-2n-3)
  (`A183160_eq`, `A199033_eq`); since `H ↦ ([tⁿ] H (1-t)^(-2n-1))ₙ` is injective (`kernel_inj`),
  the square of the substituted g.f. of a self-convolution root `a` is `(1-t)^(-2c)/((1-3t)(1+t))`,
  which gives `S` as above.

* Existence and uniqueness (`A183161_spec`, `A219197_spec`, `A183161_unique`, `A219197_unique`).
  `ψ` is onto (`ψ_mk`: by `lagrange` and `kernel_inj`, the series with coefficients
  `[tⁿ] H (1-3t)(1-t)^(-2n-1)` maps to `H`). With `K` the Catalan series (`K = 1 + x K²`),
  `(1 - 2xK)² = 1 - 4x`; substituting `x ↦ u = t²/(1-t)²` gives an integer `C` with `C² = 1 - 4u`,
  and `T = (1-t) C` satisfies `T² = (1-3t)(1+t)`. With `R = 1/T` the integer sequence
  `rootSeq c n = [tⁿ] (1-t)^(-c) R (1-3t)(1-t)^(-2n-1)` is the preimage of `(1-t)^(-c) R` under `ψ`,
  so its square has `ψ`-image `(1-t)^(-2c)/((1-3t)(1+t))`, i.e. its self-convolution is
  A183160 (`c = 0`) resp. A199033 (`c = 1`). Uniqueness: `A² = B²` with `A(0) = B(0) = 1` gives
  `(A - B)(A + B) = 0` in the domain `ℤ⟦x⟧`.

Main results: `A183161_ne_three`, `A219197_ne_three` (for the sequences `A183161 = rootSeq 0`,
`A219197 = rootSeq 1` defined here), `A183161_def_mod4`, `A219197_def_mod4` (for every integer
sequence with `a(0) = 1` and self-convolution A183160, resp. A199033), `gf_mod4` (from Hanna's
g.f.), `hanna_mod4` (coefficient form).
-/

namespace OpenProblemsLib.HannaMod4

open PowerSeries OpenProblemsLib.AutomaticMod

/-! ## The lacunary series `W` -/

/-- `wZ m = 1` iff `m ≥ 1` and `v₂(m)` is even, else `0`. -/
def wZ : ℕ → ℤ
  | 0 => 0
  | m + 1 => if (m + 1) % 2 = 1 then 1 else 1 - wZ ((m + 1) / 2)
decreasing_by omega

/-- `W = ∑_{m ≥ 1, v₂(m) even} tᵐ`. -/
noncomputable def WZ : ℤ⟦X⟧ := mk wZ

theorem WZ_add_expand : WZ + expand 2 two_ne_zero WZ = X * mk 1 := by
  ext m
  rw [map_add, coeff_expand]
  cases m with
  | zero => simp [WZ, wZ]
  | succ m =>
    rw [coeff_succ_X_mul, WZ, coeff_mk, coeff_mk, coeff_mk, wZ]
    split_ifs with h1 h2 h2
    · omega
    · simp
    · ring_nf; simp
    · omega

theorem WZ_rel : (1 - X) * (WZ + expand 2 two_ne_zero WZ) = X := by
  rw [WZ_add_expand, mul_comm, mul_assoc, mk_one_mul_one_sub_eq_one, mul_one]

theorem coeff_zero_WZ : coeff 0 WZ = 0 := by simp [WZ, wZ]

/-- `W` over `ℤ/4`. -/
noncomputable def W4 : (ZMod 4)⟦X⟧ := map (Int.castRingHom (ZMod 4)) WZ

theorem W4_rel : (1 - X) * (W4 + expand 2 two_ne_zero W4) = X := by
  have h := congrArg (map (Int.castRingHom (ZMod 4))) WZ_rel
  simpa [W4, map_mul, map_add, map_sub] using h

/-! ## `S ≡ 1 + 2W (mod 4)` -/

theorem ofNat_eq_C {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : R⟦X⟧) = C (OfNat.ofNat n) := (map_ofNat C n).symm

theorem S_mod4 (S : ℤ⟦X⟧) (h0 : constantCoeff S = 1) (hS : S ^ 2 * (1 + X) = 1 - 3 * X) :
    map (Int.castRingHom (ZMod 4)) S = 1 + 2 * W4 := by
  set φ2 := Int.castRingHom (ZMod 2)
  have h2z : (2 : (ZMod 2)⟦X⟧) = 0 := by
    rw [ofNat_eq_C, show (2 : ZMod 2) = 0 by decide, map_zero]
  have h1X : (1 + X : (ZMod 2)⟦X⟧) ≠ 0 := by
    intro h'
    have := congrArg (coeff 0) h'
    simp at this
  -- modulo 2, `S = 1`
  have hS2 : map φ2 S = 1 := by
    have h := congrArg (map φ2) hS
    rw [ofNat_eq_C (R := ℤ) 3] at h
    simp only [map_mul, map_pow, map_add, map_sub, map_one, map_X, map_C] at h
    rw [show φ2 3 = 1 by simp [φ2]; decide, map_one, one_mul] at h
    have hsq : (map φ2 S) ^ 2 = 1 := by
      have h' : (map φ2 S) ^ 2 * (1 + X) = 1 * (1 + X) := by
        rw [h]
        linear_combination (-X) * h2z
      exact mul_right_cancel₀ h1X h'
    have hz : (map φ2 S - 1) ^ 2 = 0 := by linear_combination hsq + (1 - map φ2 S) * h2z
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hz)
  -- `S = 1 + 2E` over `ℤ`
  have hS0 : coeff 0 S = 1 := by simpa using h0
  have hdiv : ∀ i, (2 : ℤ) ∣ coeff i S - (if i = 0 then 1 else 0) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simp [hS0]
    · have hc := congrArg (coeff i) hS2
      rw [coeff_map, coeff_one] at hc
      simp only [hi, ↓reduceIte] at hc ⊢
      rw [sub_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by simpa [φ2] using hc)
  set E : ℤ⟦X⟧ := mk fun i => (coeff i S - (if i = 0 then 1 else 0)) / 2 with hEdef
  have hSE : S = 1 + 2 * E := by
    ext i
    rw [map_add, coeff_one, ofNat_eq_C, coeff_C_mul, hEdef, coeff_mk,
      Int.mul_ediv_cancel' (hdiv i)]
    ring
  have hE0 : coeff 0 E = 0 := by
    rw [hEdef, coeff_mk, hS0]
    simp
  have hEE : (E + E ^ 2) * (1 + X) = -X := by
    have h4 : (4 : ℤ⟦X⟧) * ((E + E ^ 2) * (1 + X) + X) = 0 := by
      rw [hSE] at hS
      linear_combination hS
    have h4ne : (4 : ℤ⟦X⟧) ≠ 0 := by
      rw [ofNat_eq_C]
      intro h
      have := congrArg constantCoeff h
      rw [constantCoeff_C, map_zero] at this
      norm_num at this
    have := (mul_eq_zero.mp h4).resolve_left h4ne
    linear_combination this
  -- modulo 2, `E = W`
  set E2 := map φ2 E with hE2
  set W2 := map φ2 WZ with hW2
  have hW2sq : W2 ^ 2 = expand 2 two_ne_zero W2 := by
    have h := map_frobenius_expand (R := ZMod 2) (p := 2) two_ne_zero (f := W2)
    rw [ZMod.frobenius_zmod, PowerSeries.map_id] at h
    exact h.symm
  have hW2rel : (W2 + W2 ^ 2) * (1 + X) = X := by
    have h := congrArg (map φ2) WZ_rel
    simp only [map_mul, map_sub, map_add, map_one, map_X, map_expand] at h
    rw [hW2sq]
    linear_combination h + (W2 + expand 2 two_ne_zero W2) * X * h2z
  have hE2rel : (E2 + E2 ^ 2) * (1 + X) = X := by
    have h := congrArg (map φ2) hEE
    simp only [map_mul, map_add, map_pow, map_one, map_X, map_neg] at h
    linear_combination h - X * h2z
  have hunit : (1 + E2 + W2) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    rw [map_add, map_add, hE2, hW2, coeff_map, coeff_map, hE0, coeff_zero_WZ] at this
    simp at this
  have hdiff : (E2 - W2) * (1 + E2 + W2) = 0 := by
    have : ((E2 - W2) * (1 + E2 + W2)) * (1 + X) = 0 := by
      linear_combination hE2rel - hW2rel
    exact (mul_eq_zero.mp this).resolve_right h1X
  have hEW : E2 = W2 := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hunit)
  -- conclude coefficientwise
  ext i
  have hc := congrArg (coeff i) hEW
  rw [hE2, hW2, coeff_map, coeff_map] at hc
  have hd : (2 : ℤ) ∣ coeff i WZ - coeff i E :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).mp (by simpa [φ2] using hc)
  obtain ⟨k, hk⟩ := hd
  rw [coeff_map, hSE, W4, ofNat_eq_C (R := ℤ) 2, ofNat_eq_C (R := ZMod 4) 2]
  simp only [map_add, coeff_one, coeff_C_mul, coeff_map]
  have h4 : (4 : ZMod 4) = 0 := by decide
  have : coeff i E = coeff i WZ - 2 * k := by linarith
  rw [this]
  simp only [eq_intCast]
  push_cast
  split_ifs <;> linear_combination (-k : ZMod 4) * h4

/-! ## Bivariate polynomials over `ℤ/4` -/

/-- Lists `[A₀(t), A₁(t), …]` meaning `∑ xⁱ Aᵢ(t)`. -/
abbrev P2 := List (List (ZMod 4))

/-- `1 - t`. -/
def omt : P2 := [[1, -1]]
/-- `B = (1 - t)² - x`. -/
def Bl : P2 := [[1, -2, 1], [-1]]
/-- `Q = (1 - t) B`. -/
def Ql : P2 := mul2 omt Bl
/-- `Q²`. -/
def Q2l : P2 := mul2 Ql Ql
/-- `t (1 - t) B² = Q² t / (1 - t)`. -/
def c10l : P2 := mul2 [[0, 1, -1]] (mul2 Bl Bl)
/-- `-Q²`. -/
def c11l : P2 := mul2 [[-1]] Q2l

/-- The Cartier step on numerator pairs `(N₀, N₁)` (state `(N₀ + N₁ W) / Q²`). -/
def step (r : ℕ) (s : P2 × P2) : P2 × P2 :=
  (trim2 (half2 r (add2 (mul2 s.1 Q2l) (mul2 s.2 c10l))), trim2 (half2 r (mul2 s.2 c11l)))

/-- The six states (numerator pairs, trailing zeros removed). -/
def st : Fin 6 → P2 × P2 := ![
  ([[1, 3, 2, 2, 1, 3], [3, 3, 1, 1]], [[2, 2, 0, 0, 2, 2], [2, 2, 2, 2]]),
  ([[1, 0, 2, 0, 1], [3, 2, 3]], [[2, 0, 0, 0, 2], [2, 0, 2]]),
  ([[2, 2, 2, 2], [2, 2]], []),
  ([[2, 0, 0, 0, 2], [2, 0, 2]], []),
  ([[2, 2, 0, 0, 2, 2], [2, 2, 2, 2]], []),
  ([], [])]

/-- Transitions: `δ s r` is the state reached from `s` on the binary digit `r`. -/
def δ (s : Fin 6) (r : ℕ) : Fin 6 := if r = 0 then ![0, 0, 3, 4, 4, 5] s else ![1, 2, 2, 5, 3, 5] s

theorem step_ok : ∀ s : Fin 6, step 0 (st s) = st (δ s 0) ∧ step 1 (st s) = st (δ s 1) := by
  decide

theorem frob_ok : trim2 (sig2L Q2l) = trim2 (mul2 Q2l Q2l) := by decide

theorem init_ok :
    trim2 (mul2 (mul2 omt omt) Ql) = (st 0).1 ∧ trim2 (mul2 [[2]] (mul2 (mul2 omt omt) Ql)) = (st 0).2 ∧
    trim2 (mul2 omt Ql) = (st 1).1 ∧ trim2 (mul2 [[2]] (mul2 omt Ql)) = (st 1).2 := by
  decide

theorem out_ok : ∀ s : Fin 6, ((st s).1.headD []).headD 0 ≠ 3 := by decide

/-! ## The series behind the lists -/

/-- Bivariate series over `ℤ/4` (outer variable `x`, inner variable `t`). -/
abbrev S2 := (ZMod 4)⟦X⟧⟦X⟧

/-- `B = (1 - t)² - x`. -/
noncomputable def Bs : S2 := C ((1 - X) ^ 2) - X
/-- `Q = (1 - t) B`. -/
noncomputable def Qs : S2 := C (1 - X) * Bs

theorem ps2_omt : ps2 omt = C (1 - X) := by
  rw [map_sub, map_one]
  simp only [omt, ps2, ps1, map_add, map_mul, map_neg, map_one, mul_zero, add_zero]
  ring

theorem ps2_Bl : ps2 Bl = Bs := by
  simp only [Bl, Bs, ps2, ps1, map_add, map_mul, map_neg, map_one, mul_zero, add_zero,
    map_ofNat, map_sub, map_pow]
  ring

theorem ps2_Ql : ps2 Ql = Qs := by rw [Ql, ps2_mul2, ps2_omt, ps2_Bl, Qs]

theorem ps2_Q2l : ps2 Q2l = Qs ^ 2 := by rw [Q2l, ps2_mul2, ps2_Ql]; ring

theorem ps2_c10l : ps2 c10l = C X * C (1 - X) * Bs ^ 2 := by
  rw [c10l, ps2_mul2, ps2_mul2, ps2_Bl]
  simp only [ps2, ps1, map_add, map_mul, map_neg, map_one, map_zero, mul_zero, add_zero,
    map_sub]
  ring

theorem ps2_c11l : ps2 c11l = -(Qs ^ 2) := by
  rw [c11l, ps2_mul2, ps2_Q2l]
  simp only [ps2, ps1, map_neg, map_one, mul_zero, add_zero]
  ring

/-- `J = 1/(1 - t)`. -/
noncomputable def J : (ZMod 4)⟦X⟧ := mk 1

theorem J_mul : (1 - X) * J = 1 := by
  rw [mul_comm]
  exact mk_one_mul_one_sub_eq_one (ZMod 4)

/-- `B⁻¹ = ∑ₙ xⁿ (1 - t)^(-2n-2)`. -/
noncomputable def Binv : S2 := mk fun n => J ^ (2 * n + 2)

theorem B_mul_Binv : Bs * Binv = 1 := by
  ext1 n
  rw [Bs, sub_mul, map_sub, coeff_C_mul, coeff_one]
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, Binv, coeff_mk, sub_zero]
    simp only [↓reduceIte]
    rw [show 2 * 0 + 2 = 2 by rfl, ← mul_pow, J_mul, one_pow]
  | succ n =>
    rw [coeff_succ_X_mul, Binv, coeff_mk, coeff_mk]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [show 2 * (n + 1) + 2 = 2 + (2 * n + 2) by ring, pow_add, ← mul_assoc, ← mul_pow, J_mul,
      one_pow, one_mul, sub_self]

noncomputable def Qinv : S2 := C J * Binv

theorem Q_mul_Qinv : Qs * Qinv = 1 := by
  calc Qs * Qinv = C ((1 - X) * J) * (Bs * Binv) := by rw [Qs, Qinv, map_mul]; ring
    _ = 1 := by rw [J_mul, B_mul_Binv, map_one, one_mul]

/-- `U⁻¹ = Q⁻²`. -/
noncomputable def Uinv : S2 := Qinv ^ 2

theorem U_mul_Uinv : Qs ^ 2 * Uinv = 1 := by rw [Uinv, ← mul_pow, Q_mul_Qinv, one_pow]

/-- `Q⁴ = Q(x², t²)²` over `ℤ/4`. -/
theorem hM : sig2 2 two_ne_zero (Qs ^ 2) = Qs ^ 2 * Qs ^ 2 := by
  have h := congrArg ps2 frob_ok
  rwa [ps2_trim2, ps2_trim2, ps2_sig2L, ps2_mul2, ps2_Q2l] at h

/-- The Frobenius basis `(1, W)`. -/
noncomputable def e : Fin 2 → S2 := ![1, C W4]

/-- Its relation matrix: `Q² · 1 = Q² · 1(x², t²)`, `Q² W = t(1-t)B² · 1 - Q² · W(t²)`. -/
noncomputable def cm : Fin 2 → Fin 2 → S2 := ![![Qs ^ 2, 0], ![C X * C (1 - X) * Bs ^ 2, -(Qs ^ 2)]]

theorem he : ∀ i, Qs ^ 2 * e i = ∑ j, cm i j * sig2 2 two_ne_zero (e j) := by
  intro i
  fin_cases i
  · simp [e, cm, Fin.sum_univ_two]
  · simp only [e, cm, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_one, sig2_C, Fin.mk_one]
    have hC := congrArg C W4_rel
    rw [map_mul, map_add] at hC
    rw [Qs]
    linear_combination (C (1 - X) * Bs ^ 2) * hC

/-! ## The automaton -/

/-- The series of a numerator pair: `(N₀ + N₁ W) / Q²`. -/
noncomputable def val (s : P2 × P2) : S2 := (∑ i, ![ps2 s.1, ps2 s.2] i * e i) * Uinv

theorem cart2_val (r : ℕ) (hr : r < 2) (s : P2 × P2) : cart2 2 r (val s) = val (step r s) := by
  rw [val, ry_step 2 r two_ne_zero hr (Qs ^ 2) Uinv (Qs ^ 2) U_mul_Uinv hM e cm he, val, step]
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, cm,
    ps2_trim2, ps2_half2 r hr, ps2_add2, ps2_mul2, ps2_Q2l, ps2_c10l, ps2_c11l, mul_zero,
    zero_add]

/-- State `s` read at `n`: the diagonal coefficient `[xⁿ tⁿ] val (st s)`. -/
noncomputable def f (s : Fin 6) (n : ℕ) : ZMod 4 := diag (val (st s)) n

theorem f_step (s : Fin 6) (n r : ℕ) (hr : r < 2) : f s (2 * n + r) = f (δ s r) n := by
  rw [f, f, ← diag_cart2, cart2_val r hr]
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
  · rw [(step_ok s).1]
  · rw [(step_ok s).2]

theorem cc_ps2 (L : P2) : constantCoeff (constantCoeff (ps2 L)) = (L.headD []).headD 0 := by
  rcases L with _ | ⟨a, L⟩
  · simp [ps2]
  · rcases a with _ | ⟨b, a⟩ <;> simp [ps2, ps1]

theorem f_zero (s : Fin 6) : f s 0 = ((st s).1.headD []).headD 0 := by
  have hU : constantCoeff (constantCoeff Uinv) = 1 := by
    have h := congrArg (fun F : S2 => constantCoeff (constantCoeff F)) U_mul_Uinv
    simp only [map_mul, map_pow, map_one] at h
    have hQ : constantCoeff (constantCoeff Qs) = 1 := by simp [Qs, Bs]
    rw [hQ, one_pow, one_mul] at h
    exact h
  have hW : constantCoeff W4 = 0 := by
    simp [W4, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_WZ]
  simp only [f, diag, coeff_zero_eq_constantCoeff_apply]
  rw [val]
  simp only [map_mul, Fin.sum_univ_two, map_add, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, e, map_one, constantCoeff_C, hW, hU, cc_ps2]
  ring

theorem f_ne_three : ∀ n s, f s n ≠ 3 :=
  fun n s => automaton_induction 2 le_rfl f δ (fun s n r hr => f_step s n r hr) (fun _ => True)
    (fun _ _ _ _ => trivial) (· ≠ 3) (fun s _ => by rw [f_zero]; exact out_ok s) n s trivial

/-! ## The initial states -/

theorem coeff_C_mul_Binv (h : (ZMod 4)⟦X⟧) (n : ℕ) :
    diag (C h * Binv) n = coeff n (h * J ^ (2 * n + 2)) := by
  rw [diag, coeff_C_mul, Binv, coeff_mk]

theorem val_init (c : ℕ) (hc : c ≤ 1) :
    val (st (if c = 0 then 0 else 1)) = C ((1 - X) ^ (1 - c) * (1 + 2 * W4)) * Binv := by
  have hJ : ∀ m, (1 - X) ^ (m + 1) * J = (1 - X) ^ m := by
    intro m; rw [pow_succ, mul_assoc, J_mul, mul_one]
  have key : ∀ (a : (ZMod 4)⟦X⟧) (N : P2 × P2), ps2 N.1 = C (a * (1 - X)) * Qs →
      ps2 N.2 = C 2 * (C (a * (1 - X)) * Qs) →
      val N = C (a * (1 + 2 * W4)) * Binv := by
    intro a N h1 h2
    rw [val, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, e, h1, h2, Uinv, Qinv]
    calc (C (a * (1 - X)) * Qs * 1 + C 2 * (C (a * (1 - X)) * Qs) * C W4) * (C J * Binv) ^ 2
        = C (a * (1 + 2 * W4)) * C ((1 - X) * J) * (Qs * (C J * Binv)) * Binv := by
          simp only [map_mul, map_add, map_one, map_ofNat]; ring
      _ = C (a * (1 + 2 * W4)) * Binv := by
          rw [← Qinv, Q_mul_Qinv, J_mul, map_one, mul_one, mul_one]
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · show val (st 0) = _
    refine (key (1 - X) _ ?_ ?_).trans (by simp)
    · rw [← init_ok.1, ps2_trim2, ps2_mul2, ps2_mul2, ps2_omt, ps2_Ql, map_mul]
    · rw [← init_ok.2.1, ps2_trim2, ps2_mul2, ps2_mul2, ps2_mul2, ps2_omt, ps2_Ql, map_mul]
      simp only [ps2, ps1, mul_zero, add_zero, map_ofNat]
  · show val (st 1) = _
    refine (key 1 _ ?_ ?_).trans (by simp)
    · rw [← init_ok.2.2.1, ps2_trim2, ps2_mul2, ps2_omt, ps2_Ql, one_mul]
    · rw [← init_ok.2.2.2, ps2_trim2, ps2_mul2, ps2_mul2, ps2_omt, ps2_Ql, one_mul]
      simp only [ps2, ps1, mul_zero, add_zero, map_ofNat]

/-! ## Main theorem -/

/-- For `S ∈ ℤ⟦t⟧` with `S(0) = 1`, `S² (1 + t) = 1 - 3t` (so `S = √((1-3t)/(1+t))`) and
`c ∈ {0, 1}`, the integer `∑_{j ≤ n} sⱼ C(3n + c - j, n - j) = [tⁿ] S (1-t)^(-2n-1-c)` is never
`3 (mod 4)`. -/
theorem hanna_mod4 (c : ℕ) (hc : c ≤ 1) (S : ℤ⟦X⟧) (h0 : constantCoeff S = 1)
    (hS : S ^ 2 * (1 + X) = 1 - 3 * X) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), coeff j S * ((3 * n + c - j).choose (n - j) : ℤ)) % 4
      ≠ 3 := by
  intro h3
  have hcast : ((∑ j ∈ Finset.range (n + 1),
      coeff j S * ((3 * n + c - j).choose (n - j) : ℤ) : ℤ) : ZMod 4) = 3 := by
    rw [← ZMod.intCast_mod, show ((4 : ℕ) : ℤ) = 4 by rfl, h3]
    rfl
  have hval : ((∑ j ∈ Finset.range (n + 1),
      coeff j S * ((3 * n + c - j).choose (n - j) : ℤ) : ℤ) : ZMod 4) =
      f (if c = 0 then 0 else 1) n := by
    rw [f, val_init c hc, coeff_C_mul_Binv]
    have hpow : (1 - X : (ZMod 4)⟦X⟧) ^ (1 - c) * (1 + 2 * W4) * J ^ (2 * n + 2) =
        (1 + 2 * W4) * J ^ ((2 * n + c) + 1) := by
      rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
      · simp only [Nat.sub_zero, pow_one]
        linear_combination ((1 + 2 * W4) * J ^ (2 * n + 0 + 1)) * J_mul
      · simp
    rw [hpow, J, mk_one_pow_eq_mk_choose_add, coeff_mul, ← S_mod4 S h0 hS,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [coeff_map, coeff_mk, eq_intCast,
      Nat.choose_symm_of_eq_add (show 2 * n + c + (n - k) = (2 * n + c) + (n - k) by rfl),
      show 2 * n + c + (n - k) = 3 * n + c - k by omega]
  rw [hval] at hcast
  exact f_ne_three n _ hcast

/-! ## Lagrange inversion for `x = t (1 - t)²` -/

/-- `τ = t (1 - t)²`. -/
noncomputable def tau : ℤ⟦X⟧ := X * (1 - X) ^ 2

theorem constantCoeff_tau : PowerSeries.constantCoeff tau = 0 := by
  rw [tau, map_mul, PowerSeries.constantCoeff_X, zero_mul]

theorem hasSubst_tau : HasSubst tau := HasSubst.of_constantCoeff_zero' constantCoeff_tau

/-- The substitution `x ↦ t (1 - t)²`. -/
noncomputable def ψ : ℤ⟦X⟧ →ₐ[ℤ] ℤ⟦X⟧ := substAlgHom hasSubst_tau

theorem ψ_X : ψ X = tau := substAlgHom_X hasSubst_tau

theorem constantCoeff_ψ (F : ℤ⟦X⟧) : constantCoeff (ψ F) = constantCoeff F := by
  have h := constantCoeff_subst_of_constantCoeff_zero (a := tau) constantCoeff_tau F
  rw [ψ, coe_substAlgHom]
  change MvPowerSeries.constantCoeff (subst tau F) = constantCoeff F
  rw [h]
  simp

/-- `1/(1 - t)` over `ℤ`. -/
noncomputable def JZ : ℤ⟦X⟧ := mk 1

theorem JZ_mul : (1 - X) * JZ = 1 := by
  rw [mul_comm]
  exact mk_one_mul_one_sub_eq_one ℤ

theorem choose_three (d : ℕ) : (3 * d + 3).choose (d + 1) = 3 * (3 * d + 2).choose d := by
  have h : (3 * d + 3) * (3 * d + 2).choose d = (3 * d + 3).choose (d + 1) * (d + 1) :=
    Nat.add_one_mul_choose_eq (3 * d + 2) d
  have h2 : (3 * d + 3).choose (d + 1) * (d + 1) = (3 * (3 * d + 2).choose d) * (d + 1) := by
    rw [← h]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) h2

/-- `[t^d] (1 - 3t)(1 - t)^(-2d-1) = [d = 0]`. -/
theorem coeff_kernel (d : ℕ) :
    coeff d ((1 - 3 * X) * JZ ^ (2 * d + 1)) = if d = 0 then 1 else 0 := by
  rw [JZ, mk_one_pow_eq_mk_choose_add, sub_mul, one_mul, map_sub]
  cases d with
  | zero => simp
  | succ d =>
    rw [mul_assoc, ofNat_eq_C (R := ℤ) 3, coeff_C_mul, coeff_succ_X_mul, coeff_mk, coeff_mk]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [show 2 * (d + 1) + (d + 1) = 3 * d + 3 by ring,
      show 2 * (d + 1) + d = 3 * d + 2 by ring,
      Nat.choose_symm_of_eq_add (show 3 * d + 3 = 2 * (d + 1) + (d + 1) by ring),
      Nat.choose_symm_of_eq_add (show 3 * d + 2 = 2 * (d + 1) + d by ring), choose_three]
    push_cast
    ring

/-- Lagrange inversion for `x = t (1 - t)²`:
`[xⁿ] F = [tⁿ] F(t (1-t)²) (1 - 3t) (1 - t)^(-2n-1)`. -/
theorem lagrange (F : ℤ⟦X⟧) (n : ℕ) :
    coeff n F = coeff n (ψ F * (1 - 3 * X) * JZ ^ (2 * n + 1)) := by
  set R : ℤ⟦X⟧ := mk fun k => coeff (k + (n + 1)) F
  have hdec : F = ∑ m ∈ Finset.range (n + 1), C (coeff m F) * X ^ m + X ^ (n + 1) * R := by
    ext k
    rw [map_add, map_sum, coeff_X_pow_mul']
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    by_cases hk : k < n + 1
    · simp [Finset.mem_range, hk, show ¬ (n + 1 ≤ k) by omega]
    · simp only [Finset.mem_range, hk, ↓reduceIte, zero_add, show n + 1 ≤ k by omega, R,
        coeff_mk]
      rw [Nat.sub_add_cancel (by omega)]
  have hC : ∀ a : ℤ, C a = (a : ℤ⟦X⟧) := fun a => by simp
  have hterm : ∀ m ∈ Finset.range (n + 1),
      coeff n (ψ (C (coeff m F) * X ^ m) * (1 - 3 * X) * JZ ^ (2 * n + 1)) =
        if n = m then coeff m F else 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hpow : JZ ^ (2 * n + 1) = JZ ^ (2 * m) * JZ ^ (2 * (n - m) + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have h1 : ψ (C (coeff m F) * X ^ m) * (1 - 3 * X) * JZ ^ (2 * n + 1) =
        C (coeff m F) * (X ^ m * ((1 - 3 * X) * JZ ^ (2 * (n - m) + 1))) := by
      rw [map_mul, map_pow, ψ_X, tau, hpow, hC, map_intCast, ← hC, mul_pow, ← pow_mul]
      calc C (coeff m F) * (X ^ m * (1 - X) ^ (2 * m)) * (1 - 3 * X) *
            (JZ ^ (2 * m) * JZ ^ (2 * (n - m) + 1))
          = C (coeff m F) * (X ^ m * ((1 - 3 * X) * JZ ^ (2 * (n - m) + 1))) *
              ((1 - X) * JZ) ^ (2 * m) := by rw [mul_pow]; ring
        _ = _ := by rw [JZ_mul, one_pow, mul_one]
    rw [h1, coeff_C_mul, coeff_X_pow_mul', coeff_kernel]
    simp only [show m ≤ n by omega, ↓reduceIte]
    by_cases h : n = m
    · subst h; simp
    · simp [h, show n - m ≠ 0 by omega]
  have htail : coeff n (ψ (X ^ (n + 1) * R) * (1 - 3 * X) * JZ ^ (2 * n + 1)) = 0 := by
    have : ψ (X ^ (n + 1) * R) * (1 - 3 * X) * JZ ^ (2 * n + 1) =
        X ^ (n + 1) * (((1 - X) ^ 2) ^ (n + 1) * ψ R * (1 - 3 * X) * JZ ^ (2 * n + 1)) := by
      rw [map_mul, map_pow, ψ_X, tau, mul_pow]
      ring
    rw [this, coeff_X_pow_mul']
    simp
  conv_rhs => rw [hdec]
  rw [map_add ψ, add_mul, add_mul, map_add (coeff n), htail, add_zero, map_sum ψ, Finset.sum_mul,
    Finset.sum_mul, map_sum (coeff n), Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  simp

theorem uniq_cubic (u g₁ g₂ : ℤ⟦X⟧) (hu : constantCoeff u = 0) (h₁ : g₁ = 1 + u * g₁ ^ 3)
    (h₂ : g₂ = 1 + u * g₂ ^ 3) : g₁ = g₂ := by
  have h : (g₁ - g₂) * (1 - u * (g₁ ^ 2 + g₁ * g₂ + g₂ ^ 2)) = 0 := by
    linear_combination h₁ - h₂
  have hne : (1 - u * (g₁ ^ 2 + g₁ * g₂ + g₂ ^ 2)) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp [hu] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hne)

theorem ψ_G (G : ℤ⟦X⟧) (hG : G = 1 + X * G ^ 3) : ψ G = JZ := by
  have h1 : ψ G = 1 + tau * (ψ G) ^ 3 := by
    have := congrArg ψ hG
    rwa [map_add, map_one, map_mul, map_pow, ψ_X] at this
  have h2 : JZ = 1 + tau * JZ ^ 3 := by
    rw [tau]
    linear_combination (1 - X * JZ - X * (1 - X) * JZ ^ 2) * JZ_mul
  exact uniq_cubic tau _ _ (by simp [tau]) h1 h2

/-- `[tⁿ] S (1 - t)^(-2n-1-c) = ∑_{j ≤ n} sⱼ C(3n + c - j, n - j)`. -/
theorem coeff_S_J (S : ℤ⟦X⟧) (c n : ℕ) :
    coeff n (S * JZ ^ (2 * n + c + 1)) =
      ∑ j ∈ Finset.range (n + 1), coeff j S * ((3 * n + c - j).choose (n - j) : ℤ) := by
  rw [JZ, mk_one_pow_eq_mk_choose_add, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_mk, Nat.choose_symm_of_eq_add (show 2 * n + c + (n - k) = (2 * n + c) + (n - k) by rfl),
    show 2 * n + c + (n - k) = 3 * n + c - k by omega]

/-- **Generating-function form.** If `G = 1 + x G³`, `A(0) = 1` and
`A² (1 - 2x G² - 3x² G⁴) = 1` (Hanna's g.f. of A183161), then for `c ∈ {0, 1}` no coefficient
of `G^c A` (`c = 0`: A183161, `c = 1`: A219197) is `3 (mod 4)`. -/
theorem gf_mod4 (G A : ℤ⟦X⟧) (hG : G = 1 + X * G ^ 3) (hA0 : constantCoeff A = 1)
    (hA : A ^ 2 * (1 - 2 * X * G ^ 2 - 3 * X ^ 2 * G ^ 4) = 1) (c : ℕ) (hc : c ≤ 1) (n : ℕ) :
    coeff n (G ^ c * A) % 4 ≠ 3 := by
  set S := ψ A * (1 - 3 * X) with hSdef
  have hψG := ψ_G G hG
  have htJ : tau * JZ ^ 2 = X := by
    rw [tau]
    linear_combination (X * ((1 - X) * JZ + 1)) * JZ_mul
  have hψA : (ψ A) ^ 2 * (1 - 2 * X - 3 * X ^ 2) = 1 := by
    have h := congrArg ψ hA
    simp only [map_mul, map_pow, map_sub, map_one, ψ_X, hψG, map_ofNat] at h
    linear_combination h + ((ψ A) ^ 2 * (2 + 3 * tau * JZ ^ 2 + 3 * X)) * htJ
  have hS0 : constantCoeff S = 1 := by
    simp [hSdef, constantCoeff_ψ, hA0]
  have hS : S ^ 2 * (1 + X) = 1 - 3 * X := by
    rw [hSdef]
    linear_combination (1 - 3 * X) * hψA
  have hcoeff : coeff n (G ^ c * A) =
      ∑ j ∈ Finset.range (n + 1), coeff j S * ((3 * n + c - j).choose (n - j) : ℤ) := by
    rw [lagrange, ← coeff_S_J, map_mul ψ, map_pow ψ, hψG, hSdef]
    congr 1
    rw [show 2 * n + c + 1 = (2 * n + 1) + c by ring, pow_add]
    ring
  rw [hcoeff]
  exact hanna_mod4 c hc S hS0 hS n

/-! ## From the self-convolution definitions (A183160, A199033) -/

/-- `T N k = C(N-k, k) tᵏ (1-t)^(N-2k)`. -/
noncomputable def fibTerm (N k : ℕ) : ℤ⟦X⟧ := ((N - k).choose k : ℤ⟦X⟧) * X ^ k * (1 - X) ^ (N - 2 * k)

/-- `fibT N = ∑_k C(N-k, k) tᵏ (1-t)^(N-2k)` (homogenised Fibonacci polynomial). -/
noncomputable def fibT (N : ℕ) : ℤ⟦X⟧ := ∑ k ∈ Finset.range (N + 1), fibTerm N k

theorem fibTerm_eq_zero {N k : ℕ} (h : N < 2 * k) : fibTerm N k = 0 := by
  rw [fibTerm, Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem fibT_eq_range (N M : ℕ) (hM : N + 1 ≤ M) :
    fibT N = ∑ k ∈ Finset.range M, fibTerm N k := by
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    exact fibTerm_eq_zero (by omega)

theorem fibTerm_step (N k : ℕ) :
    fibTerm (N + 2) (k + 1) = (1 - X) * fibTerm (N + 1) (k + 1) + X * fibTerm N k := by
  have hP : (N + 2 - (k + 1)).choose (k + 1) = (N - k).choose k + (N - k).choose (k + 1) := by
    rcases Nat.lt_or_ge N k with h | h
    · rw [show N + 2 - (k + 1) = 0 by omega, show N - k = 0 by omega,
        Nat.choose_eq_zero_of_lt (show 0 < k by omega),
        Nat.choose_eq_zero_of_lt (show 0 < k + 1 by omega)]
    · rw [show N + 2 - (k + 1) = (N - k) + 1 by omega, Nat.choose_succ_succ]
  simp only [fibTerm]
  rw [hP, show N + 1 - (k + 1) = N - k by omega, show N + 2 - 2 * (k + 1) = N - 2 * k by omega]
  rcases Nat.lt_or_ge N (2 * k + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt (show N - k < k + 1 by omega)]
    push_cast
    ring
  · rw [show N - 2 * k = (N + 1 - 2 * (k + 1)) + 1 by omega]
    push_cast
    ring

theorem fibT_rec (N : ℕ) : fibT (N + 2) = (1 - X) * fibT (N + 1) + X * fibT N := by
  rw [fibT_eq_range (N + 1) (N + 3) (by omega), fibT_eq_range N (N + 2) (by omega), fibT,
    Finset.sum_range_succ', Finset.sum_range_succ' (fun k => fibTerm (N + 1) k) (N + 2),
    mul_add, Finset.mul_sum, Finset.mul_sum]
  have hs : ∑ k ∈ Finset.range (N + 2), fibTerm (N + 2) (k + 1) =
      ∑ k ∈ Finset.range (N + 2), (1 - X) * fibTerm (N + 1) (k + 1) +
        ∑ k ∈ Finset.range (N + 2), X * fibTerm N k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => fibTerm_step N k
  have h0 : fibTerm (N + 2) 0 = (1 - X) * fibTerm (N + 1) 0 := by
    simp only [fibTerm, Nat.sub_zero, Nat.choose_zero_right, pow_zero, mul_one, Nat.cast_one,
      one_mul, mul_zero]
    ring
  rw [hs, h0]
  ring

/-- `(1 + t) fibT N = 1 - (-t)^(N+1)`. -/
theorem fibT_closed (N : ℕ) : (1 + X) * fibT N = 1 - (-X) ^ (N + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | _ | N
    · simp [fibT, fibTerm]
    · simp [fibT, fibTerm, Finset.sum_range_succ]
      ring
    · rw [fibT_rec, mul_add, ← mul_assoc, ← mul_assoc, mul_comm (1 + X) (1 - X), mul_assoc,
        mul_comm (1 + X) X, mul_assoc, ih (N + 1) (by omega), ih N (by omega)]
      ring

/-- `1/(1 + t)`. -/
noncomputable def Pinv : ℤ⟦X⟧ := mk fun k => (-1) ^ k

theorem Pinv_mul : (1 + X) * Pinv = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => simp [Pinv]
  | succ n =>
    rw [coeff_succ_X_mul, Pinv, coeff_mk, coeff_mk, coeff_one, pow_succ]
    simp

/-- A183160 as in the entry: `∑_{k=0}^n C(n+k, n-k) C(2n-k, k)`. -/
def A183160 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((n + k).choose (n - k) * (2 * n - k).choose k : ℕ)

/-- A199033 as in the entry: `∑_{k=0}^n C(n+k+1, n-k) C(2n-k+1, k)`. -/
def A199033 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((n + k + 1).choose (n - k) * (2 * n - k + 1).choose k : ℕ)

theorem coeff_X_pow_mul_JZ (n k e : ℕ) (hk : k ≤ n) :
    coeff n (X ^ k * JZ ^ (2 * k + e + 1)) = ((n + k + e).choose (n - k) : ℤ) := by
  rw [coeff_X_pow_mul']
  simp only [hk, ↓reduceIte]
  rw [JZ, mk_one_pow_eq_mk_choose_add, coeff_mk,
    Nat.choose_symm_of_eq_add (show 2 * k + e + (n - k) = (2 * k + e) + (n - k) by rfl),
    show 2 * k + e + (n - k) = n + k + e by omega]

/-- `∑_k C(N-k, k) tᵏ (1-t)^(-2k-1-e) = fibT N (1-t)^(-N-1-e)`. -/
theorem fib_sum_J (N e : ℕ) : ∑ k ∈ Finset.range (N + 1),
    ((N - k).choose k : ℤ⟦X⟧) * (X ^ k * JZ ^ (2 * k + e + 1)) = fibT N * JZ ^ (N + e + 1) := by
  rw [fibT, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rcases Nat.lt_or_ge N (2 * k) with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), fibTerm_eq_zero h]
    simp
  · rw [fibTerm, show N + e + 1 = (N - 2 * k) + (2 * k + e + 1) by omega,
      pow_add JZ (N - 2 * k) (2 * k + e + 1)]
    calc ((N - k).choose k : ℤ⟦X⟧) * (X ^ k * JZ ^ (2 * k + e + 1))
        = ((N - k).choose k : ℤ⟦X⟧) * (X ^ k * JZ ^ (2 * k + e + 1)) *
            ((1 - X) * JZ) ^ (N - 2 * k) := by
          rw [JZ_mul, one_pow, mul_one]
      _ = _ := by rw [mul_pow]; ring

/-- `A183160(n) = [tⁿ] (1+t)⁻¹ (1-t)^(-2n-1)` and `A199033(n) = [tⁿ] (1+t)⁻¹ (1-t)^(-2n-3)`. -/
theorem A183160_eq (n : ℕ) : A183160 n = coeff n (Pinv * JZ ^ (2 * n + 1)) := by
  have hsum : (A183160 n : ℤ) = coeff n (∑ k ∈ Finset.range (2 * n + 1),
      ((2 * n - k).choose k : ℤ⟦X⟧) * (X ^ k * JZ ^ (2 * k + 0 + 1))) := by
    rw [← Finset.sum_subset (s₁ := Finset.range (n + 1)) (Finset.range_subset_range.mpr (by omega))
      (fun k hk hk' => by
        simp only [Finset.mem_range] at hk hk'
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp), map_sum, A183160]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← map_natCast (C (R := ℤ)), coeff_C_mul, coeff_X_pow_mul_JZ n k 0 (by omega)]
    push_cast
    ring_nf
  rw [hsum, fib_sum_J (2 * n) 0]
  have hf : fibT (2 * n) = (1 + X ^ (2 * n + 1)) * Pinv := by
    have h := fibT_closed (2 * n)
    calc fibT (2 * n) = ((1 + X) * Pinv) * fibT (2 * n) := by rw [Pinv_mul, one_mul]
      _ = ((1 + X) * fibT (2 * n)) * Pinv := by ring
      _ = _ := by rw [h, neg_pow, show (-1 : ℤ⟦X⟧) ^ (2 * n + 1) = -1 by
              rw [pow_succ, pow_mul]; simp]; ring
  rw [hf, show 2 * n + 0 + 1 = 2 * n + 1 by ring, add_mul, add_mul, one_mul, map_add,
    mul_assoc (X ^ (2 * n + 1)), coeff_X_pow_mul']
  simp only [show ¬ (2 * n + 1 ≤ n) by omega, ↓reduceIte, add_zero]

theorem A199033_eq (n : ℕ) : A199033 n = coeff n (Pinv * JZ ^ (2 * n + 3)) := by
  have hsum : (A199033 n : ℤ) = coeff n (∑ k ∈ Finset.range (2 * n + 1 + 1),
      ((2 * n + 1 - k).choose k : ℤ⟦X⟧) * (X ^ k * JZ ^ (2 * k + 1 + 1))) := by
    rw [← Finset.sum_subset (s₁ := Finset.range (n + 1)) (Finset.range_subset_range.mpr (by omega))
      (fun k hk hk' => by
        simp only [Finset.mem_range] at hk hk'
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp), map_sum, A199033]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← map_natCast (C (R := ℤ)), coeff_C_mul, coeff_X_pow_mul_JZ n k 1 (by omega),
      show 2 * n - k + 1 = 2 * n + 1 - k by omega]
    push_cast
    ring_nf
  rw [hsum, fib_sum_J (2 * n + 1) 1]
  have hf : fibT (2 * n + 1) = (1 - X ^ (2 * n + 2)) * Pinv := by
    have h := fibT_closed (2 * n + 1)
    calc fibT (2 * n + 1) = ((1 + X) * Pinv) * fibT (2 * n + 1) := by rw [Pinv_mul, one_mul]
      _ = ((1 + X) * fibT (2 * n + 1)) * Pinv := by ring
      _ = _ := by rw [h, neg_pow, show (-1 : ℤ⟦X⟧) ^ (2 * n + 1 + 1) = 1 by
              rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]; simp]; ring
  rw [hf, show 2 * n + 1 + 1 + 1 = 2 * n + 3 by ring, sub_mul, sub_mul, one_mul, map_sub,
    mul_assoc (X ^ (2 * n + 2)), coeff_X_pow_mul']
  simp only [show ¬ (2 * n + 2 ≤ n) by omega, ↓reduceIte, sub_zero]

/-- `H ↦ (n ↦ [tⁿ] H (1-t)^(-2n-1))` is injective. -/
theorem kernel_inj (H : ℤ⟦X⟧) (h : ∀ n, coeff n (H * JZ ^ (2 * n + 1)) = 0) : H = 0 := by
  have key : ∀ n, ∀ i ≤ n, coeff i H = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have := h 0
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
      simp only [Finset.sum_range_one] at this
      rw [show i = 0 by omega]
      simpa [JZ] using this
    | succ n ih =>
      intro i hi
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact ih i (by omega)
      have hi' : i = n + 1 := by omega
      subst hi'
      have := h (n + 1)
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
        Finset.sum_eq_zero (fun j hj => by rw [ih j (by simp at hj; omega), zero_mul])] at this
      simpa [JZ] using this
  ext n
  simpa using key n n le_rfl

/-- If `a(0) = 1` and `∑_{k ≤ n} a(k) a(n-k) = [tⁿ] K (1-t)^(-2n-1)` with
`K = (1-t)^(-2c) / (1 + t)`, then `a(n) = [tⁿ] S (1-t)^(-2n-1-c)` for an `S` with `S(0) = 1`,
`S² (1 + t) = 1 - 3t`; so `a(n) ≢ 3 (mod 4)`. -/
theorem conv_root_mod4 (c : ℕ) (hc : c ≤ 1) (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) =
      coeff n (JZ ^ (2 * c) * Pinv * JZ ^ (2 * n + 1))) (n : ℕ) : a n % 4 ≠ 3 := by
  set A : ℤ⟦X⟧ := mk a
  have hB : ∀ n, coeff n (A ^ 2) = coeff n (JZ ^ (2 * c) * Pinv * JZ ^ (2 * n + 1)) := by
    intro n
    rw [← hconv, pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [A]
  -- `ψ(A²)(1 - 3t) = (1-t)^(-2c)/(1+t)`
  have hψB : ψ (A ^ 2) * (1 - 3 * X) = JZ ^ (2 * c) * Pinv := by
    have h := kernel_inj (ψ (A ^ 2) * (1 - 3 * X) - JZ ^ (2 * c) * Pinv) (fun n => by
      rw [sub_mul, map_sub, ← lagrange, hB, sub_self])
    exact sub_eq_zero.mp h
  set S := ψ A * (1 - 3 * X) * (1 - X) ^ c with hSdef
  have hS0 : constantCoeff S = 1 := by
    simp [hSdef, constantCoeff_ψ, A, h0]
  have hS : S ^ 2 * (1 + X) = 1 - 3 * X := by
    have e1 : S ^ 2 * (1 + X) = (ψ (A ^ 2) * (1 - 3 * X)) * (1 - 3 * X) * ((1 - X) ^ c) ^ 2 * (1 + X) := by
      rw [hSdef, map_pow]; ring
    rw [e1, hψB]
    calc JZ ^ (2 * c) * Pinv * (1 - 3 * X) * ((1 - X) ^ c) ^ 2 * (1 + X)
        = (1 - 3 * X) * (((1 - X) * JZ) ^ (2 * c)) * ((1 + X) * Pinv) := by
          rw [mul_pow, ← pow_mul]; ring
      _ = 1 - 3 * X := by rw [JZ_mul, Pinv_mul, one_pow, mul_one, mul_one]
  have hcoeff : a n = ∑ j ∈ Finset.range (n + 1), coeff j S * ((3 * n + c - j).choose (n - j) : ℤ) := by
    rw [← coeff_S_J, show a n = coeff n A by simp [A], lagrange A n]
    congr 1
    rw [hSdef, show 2 * n + c + 1 = (2 * n + 1) + c by ring, pow_add JZ (2 * n + 1) c]
    calc ψ A * (1 - 3 * X) * JZ ^ (2 * n + 1)
        = ψ A * (1 - 3 * X) * JZ ^ (2 * n + 1) * ((1 - X) * JZ) ^ c := by
          rw [JZ_mul, one_pow, mul_one]
      _ = _ := by rw [mul_pow]; ring
  rw [hcoeff]
  exact hanna_mod4 c hc S hS0 hS n

/-- **A183161, from its definition.** If `a(0) = 1` and the self-convolution of `a` is
A183160 (`∑_k C(n+k, n-k) C(2n-k, k)`), then `a(n) ≢ 3 (mod 4)` for all `n`. -/
theorem A183161_def_mod4 (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) = A183160 n) (n : ℕ) :
    a n % 4 ≠ 3 :=
  conv_root_mod4 0 (by omega) a h0 (fun n => by rw [hconv, A183160_eq]; simp) n

/-- **A219197, from its definition.** If `a(0) = 1` and the self-convolution of `a` is
A199033 (`∑_k C(n+k+1, n-k) C(2n-k+1, k)`), then `a(n) ≢ 3 (mod 4)` for all `n`. -/
theorem A219197_def_mod4 (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) = A199033 n) (n : ℕ) :
    a n % 4 ≠ 3 :=
  conv_root_mod4 1 (by omega) a h0 (fun n => by
    rw [hconv, A199033_eq, show 2 * n + 3 = 2 * 1 + (2 * n + 1) by ring, pow_add]; ring_nf) n

/-! ## Existence and uniqueness of the self-convolution roots -/

/-- The Catalan generating function `K = ∑ Cat(k) xᵏ`. -/
noncomputable def catGF : ℤ⟦X⟧ := mk fun n => (catalan n : ℤ)

theorem catGF_rel : catGF = 1 + X * catGF ^ 2 := by
  ext n
  cases n with
  | zero => simp [catGF]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, pow_two, coeff_mul, catGF, coeff_mk, catalan_succ']
    simp [coeff_mk]

/-- `(1 - 2x K)² = 1 - 4x`. -/
theorem sqrt14_sq : (1 - 2 * X * catGF) ^ 2 = 1 - 4 * X := by
  linear_combination (-4 * X) * catGF_rel

/-- `u = t² (1 - t)⁻²`. -/
noncomputable def uS : ℤ⟦X⟧ := X ^ 2 * JZ ^ 2

theorem constantCoeff_uS : constantCoeff uS = 0 := by simp [uS]

theorem hasSubst_uS : HasSubst uS := HasSubst.of_constantCoeff_zero' constantCoeff_uS

/-- `C = √(1 - 4u)`, an integer series. -/
noncomputable def Cu : ℤ⟦X⟧ := substAlgHom hasSubst_uS (1 - 2 * X * catGF)

theorem Cu_sq : Cu ^ 2 = 1 - 4 * uS := by
  have h := congrArg (substAlgHom hasSubst_uS) sqrt14_sq
  rw [map_pow] at h
  rw [Cu, h, map_sub, map_one, map_mul, substAlgHom_X, map_ofNat]

theorem constantCoeff_Cu : constantCoeff Cu = 1 := by
  have h := constantCoeff_subst_of_constantCoeff_zero (a := uS) constantCoeff_uS
    (1 - 2 * X * catGF)
  rw [Cu, coe_substAlgHom]
  change MvPowerSeries.constantCoeff (subst uS (1 - 2 * X * catGF)) = 1
  rw [h]
  simp

/-- `T = (1 - t) C = √((1 - 3t)(1 + t))`. -/
noncomputable def Tsq : ℤ⟦X⟧ := (1 - X) * Cu

theorem Tsq_sq : Tsq ^ 2 = (1 - 3 * X) * (1 + X) := by
  rw [Tsq, mul_pow, Cu_sq, uS]
  linear_combination (-4 * X ^ 2 * (1 + (1 - X) * JZ)) * JZ_mul

theorem constantCoeff_Tsq : constantCoeff Tsq = 1 := by
  simp [Tsq, constantCoeff_Cu]

/-- `R = 1/√((1 - 3t)(1 + t))`. -/
noncomputable def Rr : ℤ⟦X⟧ := invOfUnit Tsq 1

theorem Rr_mul : Tsq * Rr = 1 := mul_invOfUnit Tsq 1 (by simp [constantCoeff_Tsq])

theorem constantCoeff_Rr : constantCoeff Rr = 1 := by
  have h := congrArg constantCoeff Rr_mul
  simpa [constantCoeff_Tsq] using h

theorem Rr_sq : Rr ^ 2 * (1 - 3 * X) = Pinv := by
  calc Rr ^ 2 * (1 - 3 * X) = Rr ^ 2 * ((1 - 3 * X) * (1 + X)) * Pinv := by
        linear_combination (- Rr ^ 2 * (1 - 3 * X)) * Pinv_mul
    _ = (Tsq * Rr) ^ 2 * Pinv := by rw [← Tsq_sq]; ring
    _ = Pinv := by rw [Rr_mul, one_pow, one_mul]

/-- The substitution `ψ` is onto: the series with coefficients `[tⁿ] H (1-3t)(1-t)^(-2n-1)`
is mapped to `H`. -/
theorem ψ_mk (H : ℤ⟦X⟧) :
    ψ (mk fun n => coeff n (H * (1 - 3 * X) * JZ ^ (2 * n + 1))) = H := by
  set F : ℤ⟦X⟧ := mk fun n => coeff n (H * (1 - 3 * X) * JZ ^ (2 * n + 1)) with hF
  have h := kernel_inj ((ψ F - H) * (1 - 3 * X)) (fun n => by
    rw [sub_mul, sub_mul, map_sub, ← lagrange, hF, coeff_mk, sub_self])
  have hne : (1 - 3 * X : ℤ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hne)

/-- The root sequences: `rootSeq c n = [tⁿ] (1-t)^(-c) R (1-3t) (1-t)^(-2n-1)`, integers by
construction. -/
noncomputable def rootSeq (c n : ℕ) : ℤ :=
  coeff n (JZ ^ c * Rr * (1 - 3 * X) * JZ ^ (2 * n + 1))

theorem rootSeq_spec (c : ℕ) : rootSeq c 0 = 1 ∧ ∀ n,
    ∑ k ∈ Finset.range (n + 1), rootSeq c k * rootSeq c (n - k) =
      coeff n (JZ ^ (2 * c) * Pinv * JZ ^ (2 * n + 1)) := by
  set A : ℤ⟦X⟧ := mk (rootSeq c) with hA
  have hψA : ψ A = JZ ^ c * Rr := ψ_mk (JZ ^ c * Rr)
  constructor
  · have h := constantCoeff_ψ A
    rw [hψA] at h
    have h2 : constantCoeff A = rootSeq c 0 := by simp [hA]
    rw [← h2, ← h]
    simp [constantCoeff_Rr, JZ]
  · intro n
    have hconv : ∑ k ∈ Finset.range (n + 1), rootSeq c k * rootSeq c (n - k) =
        coeff n (A ^ 2) := by
      rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [hA]
    rw [hconv, lagrange, map_pow, hψA]
    congr 1
    calc (JZ ^ c * Rr) ^ 2 * (1 - 3 * X) * JZ ^ (2 * n + 1)
        = JZ ^ (2 * c) * (Rr ^ 2 * (1 - 3 * X)) * JZ ^ (2 * n + 1) := by ring
      _ = _ := by rw [Rr_sq]

/-- Uniqueness: two integer sequences with value `1` at `0` and the same self-convolution
are equal. -/
theorem conv_root_unique (a b : ℕ → ℤ) (ha : a 0 = 1) (hb : b 0 = 1)
    (h : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) =
      ∑ k ∈ Finset.range (n + 1), b k * b (n - k)) : a = b := by
  have hsq : (mk a) ^ 2 = (mk b) ^ 2 := by
    ext n
    rw [pow_two, pow_two, coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simpa using h n
  have h0 : (mk a - mk b) * (mk a + mk b) = 0 := by linear_combination hsq
  have hne : mk a + mk b ≠ 0 := by
    intro h1
    have := congrArg constantCoeff h1
    simp [ha, hb] at this
  have := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hne)
  funext n
  simpa using congrArg (coeff n) this

/-- **A183161**, defined as an integer sequence. -/
noncomputable def A183161 (n : ℕ) : ℤ := rootSeq 0 n

/-- **A219197**, defined as an integer sequence. -/
noncomputable def A219197 (n : ℕ) : ℤ := rootSeq 1 n

/-- `A183161(0) = 1` and the self-convolution of A183161 is A183160. -/
theorem A183161_spec : A183161 0 = 1 ∧
    ∀ n, ∑ k ∈ Finset.range (n + 1), A183161 k * A183161 (n - k) = A183160 n := by
  refine ⟨(rootSeq_spec 0).1, fun n => ?_⟩
  rw [A183160_eq, show (A183161 : ℕ → ℤ) = rootSeq 0 from rfl, (rootSeq_spec 0).2 n]
  simp

/-- `A219197(0) = 1` and the self-convolution of A219197 is A199033. -/
theorem A219197_spec : A219197 0 = 1 ∧
    ∀ n, ∑ k ∈ Finset.range (n + 1), A219197 k * A219197 (n - k) = A199033 n := by
  refine ⟨(rootSeq_spec 1).1, fun n => ?_⟩
  rw [A199033_eq, show (A219197 : ℕ → ℤ) = rootSeq 1 from rfl, (rootSeq_spec 1).2 n,
    show 2 * n + 3 = 2 * 1 + (2 * n + 1) by ring, pow_add]
  ring_nf

theorem A183161_unique (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) = A183160 n) : a = A183161 :=
  conv_root_unique a A183161 h0 A183161_spec.1 fun n => by rw [hconv, A183161_spec.2]

theorem A219197_unique (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) = A199033 n) : a = A219197 :=
  conv_root_unique a A219197 h0 A219197_spec.1 fun n => by rw [hconv, A219197_spec.2]

theorem A183161_ne_three (n : ℕ) : A183161 n % 4 ≠ 3 :=
  A183161_def_mod4 A183161 A183161_spec.1 A183161_spec.2 n

theorem A219197_ne_three (n : ℕ) : A219197 n % 4 ≠ 3 :=
  A219197_def_mod4 A219197 A219197_spec.1 A219197_spec.2 n

end OpenProblemsLib.HannaMod4
