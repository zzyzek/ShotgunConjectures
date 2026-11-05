/-
OEIS A195539, Mathlib proof of R. J. Mathar's conjecture.

Definition (P. J. C. Moses' program in A195538/A195500): s = r + √(1 + r^2) with r = √8,
the regular continued fraction of s (floor algorithm over ℝ: `A195539_z`, `A195539_c`), its
convergents p_k/q_k by the standard recurrences (`A195539_P`, `A195539_Q`; the n-term
convergent FromContinuedFraction[ContinuedFraction[s, n]] is p_(n-1)/q_(n-1)), and
b(n)/a(n) = (p^2 - q^2)/(2 p q) in lowest terms with (p, q) = (p_(n-1), q_(n-1)).
A195539 is b(n) = numerator (`A195539_b`, Lean `Rat.num`).

Main theorem `A195539_main`:
* `A195539_data`: b(1..15) = 12, 35, 408, 1189, ..., 627013566048 (the printed terms);
* recurrence: b(n) = 34 b(n-2) - b(n-4) for n ≥ 5;
* b(2n+1) = A000129(4n+4) for n ≥ 0 (Pell numbers, by their recurrence);
* b(2n) = A046176(n+1) for n ≥ 1, A046176(n) = the n-th (from 1) positive m such that m^2 is
  a hexagonal number h(2h-1) (`Nat.nth`).

Proof. As for A195538 (same file structure): the continued fraction of 3 + 2√2 is
[5; 1, 4, 1, 4, ...]; with the solutions (X_k, W_k) of X^2 - 8W^2 = 1, U = X + 2W, V = X + 3W,
the convergents are p_(2k)/q_(2k) = U_(k+1)/U_k and p_(2k+1)/q_(2k+1) = V_(k+1)/V_k, and
U^2 + 4UV - 4V^2 = 1 gives lowest terms: b(2k+1) = 4V(U+2V), b(2k+2) = (U+5V)^2 - V^2
(`A195539_b_odd`, `A195539_b_even`). The addition formula for (X, W) (`A195539_XW_add`) gives
b(2k+1) = 2 W_(2k+2) = Pell(4k+4) and b(2k+2) = W_(2k+3); the hexagonal-square indices are
W_(2j+1) by the Pell classification `A195539_classify` and X_k mod 4.

Not checked: that Mathematica's FromContinuedFraction equals the recurrence convergent (the
classical identity p_k/q_k = [c_0; c_1, ..., c_k]); everything else is checked.
-/
import Mathlib

/-! ### Pell solutions of x^2 - 8 w^2 = 1 -/

/-- (X_k, W_k): (1, 0), (3, 1), (17, 6), (99, 35), ... -/
def A195539_XW : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 => (3 * (A195539_XW k).1 + 8 * (A195539_XW k).2,
      (A195539_XW k).1 + 3 * (A195539_XW k).2)

def A195539_X (k : ℕ) : ℕ := (A195539_XW k).1

def A195539_W (k : ℕ) : ℕ := (A195539_XW k).2

theorem A195539_X_succ (k : ℕ) : A195539_X (k + 1) = 3 * A195539_X k + 8 * A195539_W k := rfl

theorem A195539_W_succ (k : ℕ) : A195539_W (k + 1) = A195539_X k + 3 * A195539_W k := rfl

theorem A195539_X_zero : A195539_X 0 = 1 := rfl

theorem A195539_W_zero : A195539_W 0 = 0 := rfl

theorem A195539_inv (k : ℕ) : A195539_X k ^ 2 = 8 * A195539_W k ^ 2 + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [A195539_X_succ, A195539_W_succ]
    zify at ih ⊢
    linear_combination ih

theorem A195539_X_pos (k : ℕ) : 1 ≤ A195539_X k := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
    rw [A195539_X_succ]
    have := A195539_inv k
    nlinarith

theorem A195539_X_odd (k : ℕ) : A195539_X k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [A195539_X_succ]; omega

theorem A195539_X_mod4 (k : ℕ) : A195539_X k % 4 = if k % 2 = 0 then 1 else 3 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [A195539_X_succ]
    split_ifs at ih ⊢ <;> omega

theorem A195539_W_lt (k : ℕ) : A195539_W k < A195539_W (k + 1) := by
  rw [A195539_W_succ]
  have := A195539_X_pos k
  omega

theorem A195539_XW_lt (k : ℕ) :
    A195539_X k + 4 * A195539_W k < A195539_X (k + 1) + 4 * A195539_W (k + 1) := by
  rw [A195539_X_succ, A195539_W_succ]
  have := A195539_X_pos k
  omega

/-- Every solution of x^2 = 8 w^2 + 1 in ℕ is (X_k, W_k). -/
theorem A195539_classify :
    ∀ w x : ℕ, x ^ 2 = 8 * w ^ 2 + 1 → ∃ k, A195539_X k = x ∧ A195539_W k = w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro x hx
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · refine ⟨0, ?_, rfl⟩
      rcases x with _ | _ | x
      · simp at hx
      · rfl
      · nlinarith
    · have h1 : 8 * w ≤ 3 * x := by nlinarith
      have h2 : x ≤ 3 * w := by nlinarith
      have h3 : 2 * w < x := by nlinarith
      obtain ⟨k, hk1, hk2⟩ := ih (3 * w - x) (by omega) (3 * x - 8 * w) (by
        zify [h1, h2]
        zify at hx
        linear_combination hx)
      refine ⟨k + 1, ?_, ?_⟩
      · rw [A195539_X_succ, hk1, hk2]
        omega
      · rw [A195539_W_succ, hk1, hk2]
        omega

/-- `Nat.nth p` is f when f is strictly increasing with range {m | p m}. -/
theorem A195539_nth_eq {p : ℕ → Prop} {f : ℕ → ℕ} (hf : StrictMono f)
    (hp : ∀ m, p m ↔ ∃ k, f k = m) (n : ℕ) : Nat.nth p n = f n := by
  have hinf : (Set.ofPred p).Infinite :=
    (Set.infinite_range_of_injective hf.injective).mono (by
      rintro _ ⟨k, rfl⟩
      exact (hp _).2 ⟨k, rfl⟩)
  have h := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := p) f ?_ ?_ (hf.strictMonoOn _)
  · exact (h (show n ∈ {n : ℕ | ∀ hf : (Set.ofPred p).Finite, n < hf.toFinset.card} from
      fun hfin => absurd hfin hinf)).symm
  · intro m hm
    obtain ⟨k, rfl⟩ := (hp m).1 hm
    exact ⟨k, fun hfin => absurd hfin hinf, rfl⟩
  · intro k _
    exact (hp _).2 ⟨k, rfl⟩

/-! ### The continued fraction of 3 + 2√2 -/

/-- Complete quotients: z_0 = √8 + √(1 + √8^2), z_(k+1) = 1/(z_k - ⌊z_k⌋). -/
noncomputable def A195539_z : ℕ → ℝ
  | 0 => Real.sqrt 8 + Real.sqrt (1 + Real.sqrt 8 ^ 2)
  | k + 1 => 1 / (A195539_z k - ⌊A195539_z k⌋)

/-- Partial quotients. -/
noncomputable def A195539_c (k : ℕ) : ℤ := ⌊A195539_z k⌋

/-- Convergent numerators. -/
noncomputable def A195539_P : ℕ → ℤ
  | 0 => A195539_c 0
  | 1 => A195539_c 1 * A195539_c 0 + 1
  | k + 2 => A195539_c (k + 2) * A195539_P (k + 1) + A195539_P k

/-- Convergent denominators. -/
noncomputable def A195539_Q : ℕ → ℤ
  | 0 => 1
  | 1 => A195539_c 1
  | k + 2 => A195539_c (k + 2) * A195539_Q (k + 1) + A195539_Q k

/-- b(n)/a(n) = (p^2 - q^2)/(2 p q) with p/q the n-term convergent. -/
noncomputable def A195539_frac (n : ℕ) : ℚ :=
  ((A195539_P (n - 1) ^ 2 - A195539_Q (n - 1) ^ 2 : ℤ) : ℚ) /
    ((2 * A195539_P (n - 1) * A195539_Q (n - 1) : ℤ) : ℚ)

/-- A195539: numerators. -/
noncomputable def A195539_b (n : ℕ) : ℤ := (A195539_frac n).num

theorem A195539_sqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem A195539_sqrt2_bounds : 1.4 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem A195539_z0 : A195539_z 0 = 3 + 2 * Real.sqrt 2 := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h9 : Real.sqrt (1 + Real.sqrt 8 ^ 2) = 3 := by
    rw [Real.sq_sqrt (by norm_num), show (1 + 8 : ℝ) = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [A195539_z, h9, h8]
  ring

theorem A195539_floor_of {y : ℝ} {t : ℤ} (h1 : (t : ℝ) ≤ y) (h2 : y < t + 1) : ⌊y⌋ = t := by
  rw [Int.floor_eq_iff]
  exact ⟨h1, h2⟩

theorem A195539_z_odd (k : ℕ) : A195539_z (2 * k + 1) = (Real.sqrt 2 + 1) / 2 := by
  obtain ⟨hl, hu⟩ := A195539_sqrt2_bounds
  have hs := A195539_sqrt2
  induction k with
  | zero =>
    have hf : ⌊(3 + 2 * Real.sqrt 2 : ℝ)⌋ = 5 :=
      A195539_floor_of (by push_cast; linarith) (by push_cast; linarith)
    rw [show 2 * 0 + 1 = 0 + 1 by rfl, A195539_z, A195539_z0, hf]
    rw [one_div]
    apply inv_eq_of_mul_eq_one_right
    push_cast
    linear_combination hs
  | succ k ih =>
    have e1 : A195539_z (2 * k + 2) = 2 + 2 * Real.sqrt 2 := by
      have hf : ⌊((Real.sqrt 2 + 1) / 2 : ℝ)⌋ = 1 :=
        A195539_floor_of (by push_cast; linarith) (by push_cast; linarith)
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, A195539_z, ih, hf]
      rw [one_div]
      apply inv_eq_of_mul_eq_one_right
      push_cast
      linear_combination hs
    have hf : ⌊(2 + 2 * Real.sqrt 2 : ℝ)⌋ = 4 :=
      A195539_floor_of (by push_cast; linarith) (by push_cast; linarith)
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, A195539_z, e1, hf]
    rw [one_div]
    apply inv_eq_of_mul_eq_one_right
    push_cast
    linear_combination hs

theorem A195539_c_val (k : ℕ) :
    A195539_c 0 = 5 ∧ A195539_c (2 * k + 1) = 1 ∧ A195539_c (2 * k + 2) = 4 := by
  obtain ⟨hl, hu⟩ := A195539_sqrt2_bounds
  have hs := A195539_sqrt2
  refine ⟨?_, ?_, ?_⟩
  · unfold A195539_c
    rw [A195539_z0]
    exact A195539_floor_of (by push_cast; linarith) (by push_cast; linarith)
  · unfold A195539_c
    rw [A195539_z_odd]
    exact A195539_floor_of (by push_cast; linarith) (by push_cast; linarith)
  · unfold A195539_c
    have hf : ⌊((Real.sqrt 2 + 1) / 2 : ℝ)⌋ = 1 :=
      A195539_floor_of (by push_cast; linarith) (by push_cast; linarith)
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, A195539_z, A195539_z_odd, hf]
    have e : 1 / ((Real.sqrt 2 + 1) / 2 - ((1 : ℤ) : ℝ)) = 2 + 2 * Real.sqrt 2 := by
      rw [one_div]
      apply inv_eq_of_mul_eq_one_right
      push_cast
      linear_combination hs
    rw [e]
    exact A195539_floor_of (by push_cast; linarith) (by push_cast; linarith)

/-! ### Convergents in terms of (X, W) -/

def A195539_U (k : ℕ) : ℤ := (A195539_X k : ℤ) + 2 * A195539_W k

def A195539_V (k : ℕ) : ℤ := (A195539_X k : ℤ) + 3 * A195539_W k

theorem A195539_U_succ (k : ℕ) : A195539_U (k + 1) = A195539_U k + 4 * A195539_V k := by
  unfold A195539_U A195539_V
  rw [A195539_X_succ, A195539_W_succ]
  push_cast
  ring

theorem A195539_V_succ (k : ℕ) : A195539_V (k + 1) = A195539_U k + 5 * A195539_V k := by
  unfold A195539_U A195539_V
  rw [A195539_X_succ, A195539_W_succ]
  push_cast
  ring

theorem A195539_U_step (k m : ℕ) (h : m = k + 1) :
    A195539_U m = A195539_U k + 4 * A195539_V k := by
  subst h
  exact A195539_U_succ k

theorem A195539_V_step (k m : ℕ) (h : m = k + 1) :
    A195539_V m = A195539_U k + 5 * A195539_V k := by
  subst h
  exact A195539_V_succ k

theorem A195539_UV_inv (k : ℕ) :
    A195539_U k ^ 2 + 4 * A195539_U k * A195539_V k - 4 * A195539_V k ^ 2 = 1 := by
  have h := A195539_inv k
  zify at h
  unfold A195539_U A195539_V
  linear_combination h

theorem A195539_U_pos (k : ℕ) : 0 < A195539_U k := by
  unfold A195539_U
  have := A195539_X_pos k
  omega

theorem A195539_V_pos (k : ℕ) : 0 < A195539_V k := by
  unfold A195539_V
  have := A195539_X_pos k
  omega

theorem A195539_P_succ_succ (n : ℕ) :
    A195539_P (n + 2) = A195539_c (n + 2) * A195539_P (n + 1) + A195539_P n := by
  rw [A195539_P]

theorem A195539_Q_succ_succ (n : ℕ) :
    A195539_Q (n + 2) = A195539_c (n + 2) * A195539_Q (n + 1) + A195539_Q n := by
  rw [A195539_Q]

theorem A195539_PQ (k : ℕ) :
    A195539_P (2 * k) = A195539_U (k + 1) ∧ A195539_P (2 * k + 1) = A195539_V (k + 1) ∧
    A195539_Q (2 * k) = A195539_U k ∧ A195539_Q (2 * k + 1) = A195539_V k := by
  induction k with
  | zero =>
    obtain ⟨h0, h1, -⟩ := A195539_c_val 0
    refine ⟨?_, ?_, rfl, ?_⟩
    · show A195539_c 0 = _
      rw [h0]
      decide
    · show A195539_c 1 * A195539_c 0 + 1 = _
      rw [h0, h1]
      decide
    · show A195539_c 1 = _
      rw [h1]
      decide
  | succ k ih =>
    obtain ⟨-, h1, h2⟩ := A195539_c_val k
    obtain ⟨-, h1', -⟩ := A195539_c_val (k + 1)
    obtain ⟨ihP0, ihP1, ihQ0, ihQ1⟩ := ih
    have eP0 : A195539_P (2 * (k + 1)) = A195539_U (k + 1 + 1) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, A195539_P_succ_succ, h2, ihP1, ihP0,
        A195539_U_succ (k + 1)]
      ring
    have eQ0 : A195539_Q (2 * (k + 1)) = A195539_U (k + 1) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, A195539_Q_succ_succ, h2, ihQ1, ihQ0,
        A195539_U_succ k]
      ring
    refine ⟨eP0, ?_, eQ0, ?_⟩
    · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, A195539_P_succ_succ,
        show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, h1',
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring, eP0, ihP1, A195539_V_succ (k + 1),
        A195539_U_succ (k + 1)]
      ring
    · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, A195539_Q_succ_succ,
        show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, h1',
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring, eQ0, ihQ1, A195539_V_succ k,
        A195539_U_succ k]
      ring

/-! ### Lowest terms -/

theorem A195539_num_eq {N D : ℤ} {p q : ℤ} (hD : 0 < D) (hc : IsCoprime N D)
    (he : ((p ^ 2 - q ^ 2 : ℤ) : ℚ) / ((2 * p * q : ℤ) : ℚ) = (N : ℚ) / (D : ℚ)) :
    (((p ^ 2 - q ^ 2 : ℤ) : ℚ) / ((2 * p * q : ℤ) : ℚ)).num = N := by
  rw [he]
  exact Rat.num_div_eq_of_coprime hD (Int.isCoprime_iff_gcd_eq_one.mp hc)

theorem A195539_b_odd (k : ℕ) :
    A195539_b (2 * k + 1) = 4 * A195539_V k * (A195539_U k + 2 * A195539_V k) := by
  obtain ⟨hP, -, hQ, -⟩ := A195539_PQ k
  have hI := A195539_UV_inv k
  have hU := A195539_U_pos k
  have hV := A195539_V_pos k
  unfold A195539_b A195539_frac
  rw [show 2 * k + 1 - 1 = 2 * k by omega, hP, hQ, A195539_U_succ]
  generalize A195539_U k = U at hI hU hV ⊢
  generalize A195539_V k = V at hI hU hV ⊢
  apply A195539_num_eq (D := (U + 4 * V) * U) (mul_pos (by linarith) hU)
  · have c1 : IsCoprime V (U + 4 * V) := ⟨-4 * V, U, by linear_combination hI⟩
    have c2 : IsCoprime V U := ⟨-4 * V, U + 4 * V, by linear_combination hI⟩
    have c3 : IsCoprime (4 : ℤ) (U + 4 * V) := ⟨-V ^ 2, U, by linear_combination hI⟩
    have c4 : IsCoprime (4 : ℤ) U := ⟨-V ^ 2, U + 4 * V, by linear_combination hI⟩
    have c5 : IsCoprime (U + 2 * V) (U + 4 * V) := ⟨U + 6 * V, -4 * V, by linear_combination hI⟩
    have c6 : IsCoprime (U + 2 * V) U := ⟨-2 * V, U + 6 * V, by linear_combination hI⟩
    exact IsCoprime.mul_right (IsCoprime.mul_left (IsCoprime.mul_left c3 c1) c5)
      (IsCoprime.mul_left (IsCoprime.mul_left c4 c2) c6)
  · have hUq : (0 : ℚ) < U := by exact_mod_cast hU
    have hVq : (0 : ℚ) < V := by exact_mod_cast hV
    push_cast
    rw [div_eq_div_iff (mul_pos (mul_pos two_pos (by linarith)) hUq).ne'
      (mul_pos (by linarith) hUq).ne']
    ring

theorem A195539_b_even (k : ℕ) :
    A195539_b (2 * k + 2) = (A195539_U k + 5 * A195539_V k) ^ 2 - A195539_V k ^ 2 := by
  obtain ⟨-, hP, -, hQ⟩ := A195539_PQ k
  have hI := A195539_UV_inv k
  have hU := A195539_U_pos k
  have hV := A195539_V_pos k
  unfold A195539_b A195539_frac
  rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega, hP, hQ, A195539_V_succ]
  generalize A195539_U k = U at hI hU hV ⊢
  generalize A195539_V k = V at hI hU hV ⊢
  apply A195539_num_eq (D := 2 * (U + 5 * V) * V)
    (mul_pos (mul_pos two_pos (by linarith)) hV)
  · rw [show (U + 5 * V) ^ 2 - V ^ 2 = (U + 4 * V) * (U + 6 * V) by ring]
    have c1 : IsCoprime (U + 4 * V) 2 := ⟨U, -2 * V ^ 2, by linear_combination hI⟩
    have c2 : IsCoprime (U + 6 * V) 2 := ⟨U, -2 * V ^ 2 - U * V, by linear_combination hI⟩
    have c3 : IsCoprime (U + 4 * V) (U + 5 * V) := ⟨U + 4 * V, -4 * V, by linear_combination hI⟩
    have c4 : IsCoprime (U + 6 * V) (U + 5 * V) := ⟨U + 6 * V, -8 * V, by linear_combination hI⟩
    have c5 : IsCoprime (U + 4 * V) V := ⟨U, -4 * V, by linear_combination hI⟩
    have c6 : IsCoprime (U + 6 * V) V := ⟨U, -2 * U - 4 * V, by linear_combination hI⟩
    exact IsCoprime.mul_left (IsCoprime.mul_right (IsCoprime.mul_right c1 c3) c5)
      (IsCoprime.mul_right (IsCoprime.mul_right c2 c4) c6)
  · rfl

/-! ### Data and recurrence -/

/-- Closed form of b(n) (computable). -/
def A195539_bf (n : ℕ) : ℤ :=
  if n % 2 = 1 then
    4 * ((A195539_X (n / 2) : ℤ) + 3 * A195539_W (n / 2)) *
      (3 * (A195539_X (n / 2) : ℤ) + 8 * A195539_W (n / 2))
  else
    (6 * (A195539_X (n / 2 - 1) : ℤ) + 17 * A195539_W (n / 2 - 1)) ^ 2 -
      ((A195539_X (n / 2 - 1) : ℤ) + 3 * A195539_W (n / 2 - 1)) ^ 2

theorem A195539_b_eq_bf (n : ℕ) (hn : 1 ≤ n) : A195539_b n = A195539_bf n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain rfl : n = 2 * j + 2 := by omega
    rw [A195539_b_even]
    unfold A195539_bf A195539_U A195539_V
    rw [ite_eq_right (by omega), show (2 * j + 2) / 2 - 1 = j by omega]
    ring
  · subst hk
    rw [A195539_b_odd]
    unfold A195539_bf A195539_U A195539_V
    rw [ite_eq_left (by omega), show (2 * k + 1) / 2 = k by omega]
    ring

theorem A195539_data :
    (List.range 15).map (fun i => A195539_b (i + 1)) =
      [12, 35, 408, 1189, 13860, 40391, 470832, 1372105, 15994428, 46611179,
       543339720, 1583407981, 18457556052, 53789260175, 627013566048] := by
  rw [List.map_congr_left (g := fun i => A195539_bf (i + 1))
    (fun i _ => A195539_b_eq_bf (i + 1) (by omega))]
  decide

theorem A195539_rec (n : ℕ) (hn : 5 ≤ n) :
    A195539_b n = 34 * A195539_b (n - 2) - A195539_b (n - 4) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    obtain rfl : n = 2 * (j + 2) + 2 := by omega
    rw [show 2 * (j + 2) + 2 - 2 = 2 * (j + 1) + 2 by omega,
      show 2 * (j + 2) + 2 - 4 = 2 * j + 2 by omega,
      A195539_b_even, A195539_b_even, A195539_b_even,
      A195539_U_step (j + 1) (j + 2) rfl, A195539_V_step (j + 1) (j + 2) rfl,
      A195539_U_step j (j + 1) rfl, A195539_V_step j (j + 1) rfl]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    subst hk
    rw [show 2 * (j + 2) + 1 - 2 = 2 * (j + 1) + 1 by omega,
      show 2 * (j + 2) + 1 - 4 = 2 * j + 1 by omega,
      A195539_b_odd, A195539_b_odd, A195539_b_odd,
      A195539_U_step (j + 1) (j + 2) rfl, A195539_V_step (j + 1) (j + 2) rfl,
      A195539_U_step j (j + 1) rfl, A195539_V_step j (j + 1) rfl]
    ring

/-! ### Addition formula and the bisections -/

theorem A195539_XW_add (a b : ℕ) :
    A195539_X (a + b) = A195539_X a * A195539_X b + 8 * A195539_W a * A195539_W b ∧
    A195539_W (a + b) = A195539_X a * A195539_W b + A195539_W a * A195539_X b := by
  induction b with
  | zero => simp [A195539_X_zero, A195539_W_zero]
  | succ b ih =>
    rw [← add_assoc, A195539_X_succ, A195539_W_succ, A195539_X_succ, A195539_W_succ, ih.1, ih.2]
    constructor <;> ring

/-- Pell numbers A000129: 0, 1, then a(n) = 2 a(n-1) + a(n-2). -/
def A000129 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * A000129 (n + 1) + A000129 n

theorem A195539_pell (j : ℕ) :
    A000129 (2 * j) = 2 * (A195539_W j : ℤ) ∧
    A000129 (2 * j + 1) = (A195539_X j : ℤ) + 2 * A195539_W j := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    have e0 : A000129 (2 * (j + 1)) = 2 * A000129 (2 * j + 1) + A000129 (2 * j) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, A000129]
    have e1 : A000129 (2 * (j + 1) + 1) = 2 * A000129 (2 * (j + 1)) + A000129 (2 * j + 1) := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, A000129,
        show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    rw [A195539_X_succ, A195539_W_succ]
    push_cast
    constructor
    · rw [e0, ih.1, ih.2]
      ring
    · rw [e1, e0, ih.1, ih.2]
      ring

/-- Positive m such that m^2 is hexagonal. -/
def A195539_S3 (m : ℕ) : Prop := 0 < m ∧ ∃ h : ℕ, (m : ℤ) ^ 2 = h * (2 * h - 1)

/-- A046176 (offset 1). -/
noncomputable def A046176 (n : ℕ) : ℕ := Nat.nth A195539_S3 (n - 1)

def A195539_f3 (j : ℕ) : ℕ := A195539_W (2 * j + 1)

theorem A195539_f3_mono : StrictMono A195539_f3 := by
  have hW : StrictMono A195539_W := strictMono_nat_of_lt_succ A195539_W_lt
  intro i j hij
  exact hW (by omega)

theorem A195539_S3_iff (m : ℕ) : A195539_S3 m ↔ ∃ j, A195539_f3 j = m := by
  constructor
  · rintro ⟨hm, h, hh⟩
    have h1 : 1 ≤ h := by
      rcases Nat.eq_zero_or_pos h with rfl | hp
      · simp at hh
        omega
      · exact hp
    obtain ⟨k, hk1, hk2⟩ := A195539_classify m (4 * h - 1) (by
      zify [show 1 ≤ 4 * h by omega]
      linear_combination -8 * hh)
    have h4 := A195539_X_mod4 k
    rw [hk1] at h4
    have hk : k % 2 = 1 := by
      by_contra hc
      rw [ite_eq_left (by omega)] at h4
      omega
    refine ⟨k / 2, ?_⟩
    unfold A195539_f3
    rw [show 2 * (k / 2) + 1 = k by omega, hk2]
  · rintro ⟨j, rfl⟩
    have h4 := A195539_X_mod4 (2 * j + 1)
    rw [ite_eq_right (by omega)] at h4
    have hI := A195539_inv (2 * j + 1)
    refine ⟨?_, (A195539_X (2 * j + 1) + 1) / 4, ?_⟩
    · unfold A195539_f3
      rw [A195539_W_succ]
      have := A195539_X_pos (2 * j)
      omega
    · unfold A195539_f3
      have e : 4 * ((A195539_X (2 * j + 1) + 1) / 4) = A195539_X (2 * j + 1) + 1 := by omega
      generalize (A195539_X (2 * j + 1) + 1) / 4 = h at e ⊢
      generalize A195539_X (2 * j + 1) = X at e hI
      generalize A195539_W (2 * j + 1) = W at hI ⊢
      zify at e hI
      have : 8 * (W : ℤ) ^ 2 = 8 * ((h : ℤ) * (2 * h - 1)) := by
        linear_combination -hI - ((X : ℤ) + 4 * h - 1) * e
      linarith

/-! ### Main theorem -/

theorem A195539_main :
    (List.range 15).map (fun i => A195539_b (i + 1)) =
      [12, 35, 408, 1189, 13860, 40391, 470832, 1372105, 15994428, 46611179,
       543339720, 1583407981, 18457556052, 53789260175, 627013566048] ∧
    (∀ n, 5 ≤ n → A195539_b n = 34 * A195539_b (n - 2) - A195539_b (n - 4)) ∧
    (∀ n, A195539_b (2 * n + 1) = A000129 (4 * n + 4)) ∧
    (∀ n, 1 ≤ n → A195539_b (2 * n) = A046176 (n + 1)) := by
  refine ⟨A195539_data, A195539_rec, ?_, ?_⟩
  · intro n
    rw [A195539_b_odd, show 4 * n + 4 = 2 * (n + 2 + n) by ring, (A195539_pell _).1,
      (A195539_XW_add (n + 2) n).2]
    have hX2 : A195539_X (n + 2) = 17 * A195539_X n + 48 * A195539_W n := by
      rw [A195539_X_succ, A195539_X_succ, A195539_W_succ]
      ring
    have hW2 : A195539_W (n + 2) = 6 * A195539_X n + 17 * A195539_W n := by
      rw [A195539_W_succ, A195539_X_succ, A195539_W_succ]
      ring
    rw [hX2, hW2]
    unfold A195539_U A195539_V
    push_cast
    ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    unfold A046176
    rw [show k + 1 + 1 - 1 = k + 1 by omega, A195539_nth_eq A195539_f3_mono A195539_S3_iff,
      show 2 * (k + 1) = 2 * k + 2 by ring, A195539_b_even]
    unfold A195539_f3
    rw [show 2 * (k + 1) + 1 = (k + 3) + k by ring, (A195539_XW_add (k + 3) k).2]
    have hX3 : A195539_X (k + 3) = 99 * A195539_X k + 280 * A195539_W k := by
      have e : A195539_X (k + 3) =
          3 * (3 * (3 * A195539_X k + 8 * A195539_W k) + 8 * (A195539_X k + 3 * A195539_W k)) +
          8 * ((3 * A195539_X k + 8 * A195539_W k) + 3 * (A195539_X k + 3 * A195539_W k)) := rfl
      rw [e]
      ring
    have hW3 : A195539_W (k + 3) = 35 * A195539_X k + 99 * A195539_W k := by
      have e : A195539_W (k + 3) =
          (3 * (3 * A195539_X k + 8 * A195539_W k) + 8 * (A195539_X k + 3 * A195539_W k)) +
          3 * ((3 * A195539_X k + 8 * A195539_W k) + 3 * (A195539_X k + 3 * A195539_W k)) := rfl
      rw [e]
      ring
    rw [hX3, hW3]
    unfold A195539_U A195539_V
    push_cast
    ring
