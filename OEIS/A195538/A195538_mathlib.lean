/-
OEIS A195538, Mathlib proof of R. J. Mathar's conjecture.

Definition (P. J. C. Moses' program in A195538/A195500): s = r + √(1 + r^2) with r = √8,
the regular continued fraction of s (floor algorithm over ℝ: `A195538_z`, `A195538_c`), its
convergents p_k/q_k by the standard recurrences (`A195538_P`, `A195538_Q`; the n-term
convergent FromContinuedFraction[ContinuedFraction[s, n]] is p_(n-1)/q_(n-1)), and
b(n)/a(n) = (p^2 - q^2)/(2 p q) in lowest terms with (p, q) = (p_(n-1), q_(n-1)).
a(n) = denominator (`A195538_a`, Lean `Rat.den`), b(n) = numerator.

Main theorem `A195538_main`:
* `A195538_data`: a(1..16) = 5, 12, 145, 420, ..., 646030941360 (the printed terms);
* recurrence: a(n) = 35 a(n-2) - 35 a(n-4) + a(n-6) for n ≥ 7;
* bisection A098602: a(2k) = A098602(k) for k ≥ 1, with A098602(n) = A001652(n) A046090(n),
  A001652 by its recurrence x(n) = 6x(n-1) - x(n-2) + 2, x(0) = 0, x(1) = 3, and A046090(n) =
  the n-th (from 0) value X+1 over Pythagorean triples (X, X+1, Z) (`Nat.nth`; ordering by Z
  is ordering by X);
* bisection A076218: a(2k-1) = A076218(k+2) for k ≥ 1, A076218(n) = the n-th (from 1) number m
  with 2m^2 - 3m + 1 a square (`Nat.nth`).

Proof. The continued fraction of 3 + 2√2 is [5; 1, 4, 1, 4, ...] (`A195538_c_val`). With the
solutions (X_k, W_k) of X^2 - 8W^2 = 1 (`A195538_XW`, (1,0), (3,1), (17,6), ...), U = X + 2W,
V = X + 3W: p_(2k) = U_(k+1), q_(2k) = U_k, p_(2k+1) = V_(k+1), q_(2k+1) = V_k (`A195538_PQ`).
U^2 + 4UV - 4V^2 = 1 gives the coprimality needed for lowest terms, so
a(2k+1) = (U+4V) U and a(2k+2) = 2 (U+5V) V (`A195538_a_odd`, `A195538_a_even`).
The recurrence is a polynomial identity. The bisection sets are described by the Pell
classification `A195538_classify` (descent (x, w) ↦ (3x - 8w, 3w - x)).

Not checked: that Mathematica's FromContinuedFraction equals the recurrence convergent (the
classical identity p_k/q_k = [c_0; c_1, ..., c_k]); everything else is checked.
-/
import Mathlib

/-! ### Pell solutions of x^2 - 8 w^2 = 1 -/

/-- (X_k, W_k): (1, 0), (3, 1), (17, 6), (99, 35), ... -/
def A195538_XW : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 => (3 * (A195538_XW k).1 + 8 * (A195538_XW k).2,
      (A195538_XW k).1 + 3 * (A195538_XW k).2)

def A195538_X (k : ℕ) : ℕ := (A195538_XW k).1

def A195538_W (k : ℕ) : ℕ := (A195538_XW k).2

theorem A195538_X_succ (k : ℕ) : A195538_X (k + 1) = 3 * A195538_X k + 8 * A195538_W k := rfl

theorem A195538_W_succ (k : ℕ) : A195538_W (k + 1) = A195538_X k + 3 * A195538_W k := rfl

theorem A195538_X_zero : A195538_X 0 = 1 := rfl

theorem A195538_W_zero : A195538_W 0 = 0 := rfl

theorem A195538_inv (k : ℕ) : A195538_X k ^ 2 = 8 * A195538_W k ^ 2 + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [A195538_X_succ, A195538_W_succ]
    zify at ih ⊢
    linear_combination ih

theorem A195538_X_pos (k : ℕ) : 1 ≤ A195538_X k := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
    rw [A195538_X_succ]
    have := A195538_inv k
    nlinarith

theorem A195538_X_odd (k : ℕ) : A195538_X k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [A195538_X_succ]; omega

theorem A195538_X_mod4 (k : ℕ) : A195538_X k % 4 = if k % 2 = 0 then 1 else 3 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [A195538_X_succ]
    split_ifs at ih ⊢ <;> omega

theorem A195538_W_lt (k : ℕ) : A195538_W k < A195538_W (k + 1) := by
  rw [A195538_W_succ]
  have := A195538_X_pos k
  omega

theorem A195538_XW_lt (k : ℕ) :
    A195538_X k + 4 * A195538_W k < A195538_X (k + 1) + 4 * A195538_W (k + 1) := by
  rw [A195538_X_succ, A195538_W_succ]
  have := A195538_X_pos k
  omega

/-- Every solution of x^2 = 8 w^2 + 1 in ℕ is (X_k, W_k). -/
theorem A195538_classify :
    ∀ w x : ℕ, x ^ 2 = 8 * w ^ 2 + 1 → ∃ k, A195538_X k = x ∧ A195538_W k = w := by
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
      · rw [A195538_X_succ, hk1, hk2]
        omega
      · rw [A195538_W_succ, hk1, hk2]
        omega

/-- `Nat.nth p` is f when f is strictly increasing with range {m | p m}. -/
theorem A195538_nth_eq {p : ℕ → Prop} {f : ℕ → ℕ} (hf : StrictMono f)
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
noncomputable def A195538_z : ℕ → ℝ
  | 0 => Real.sqrt 8 + Real.sqrt (1 + Real.sqrt 8 ^ 2)
  | k + 1 => 1 / (A195538_z k - ⌊A195538_z k⌋)

/-- Partial quotients. -/
noncomputable def A195538_c (k : ℕ) : ℤ := ⌊A195538_z k⌋

/-- Convergent numerators. -/
noncomputable def A195538_P : ℕ → ℤ
  | 0 => A195538_c 0
  | 1 => A195538_c 1 * A195538_c 0 + 1
  | k + 2 => A195538_c (k + 2) * A195538_P (k + 1) + A195538_P k

/-- Convergent denominators. -/
noncomputable def A195538_Q : ℕ → ℤ
  | 0 => 1
  | 1 => A195538_c 1
  | k + 2 => A195538_c (k + 2) * A195538_Q (k + 1) + A195538_Q k

/-- b(n)/a(n) = (p^2 - q^2)/(2 p q) with p/q the n-term convergent. -/
noncomputable def A195538_frac (n : ℕ) : ℚ :=
  ((A195538_P (n - 1) ^ 2 - A195538_Q (n - 1) ^ 2 : ℤ) : ℚ) /
    ((2 * A195538_P (n - 1) * A195538_Q (n - 1) : ℤ) : ℚ)

/-- A195538: denominators. -/
noncomputable def A195538_a (n : ℕ) : ℕ := (A195538_frac n).den

theorem A195538_sqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem A195538_sqrt2_bounds : 1.4 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem A195538_z0 : A195538_z 0 = 3 + 2 * Real.sqrt 2 := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h9 : Real.sqrt (1 + Real.sqrt 8 ^ 2) = 3 := by
    rw [Real.sq_sqrt (by norm_num), show (1 + 8 : ℝ) = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [A195538_z, h9, h8]
  ring

theorem A195538_floor_of {y : ℝ} {t : ℤ} (h1 : (t : ℝ) ≤ y) (h2 : y < t + 1) : ⌊y⌋ = t := by
  rw [Int.floor_eq_iff]
  exact ⟨h1, h2⟩

theorem A195538_z_odd (k : ℕ) : A195538_z (2 * k + 1) = (Real.sqrt 2 + 1) / 2 := by
  obtain ⟨hl, hu⟩ := A195538_sqrt2_bounds
  have hs := A195538_sqrt2
  induction k with
  | zero =>
    have hf : ⌊(3 + 2 * Real.sqrt 2 : ℝ)⌋ = 5 :=
      A195538_floor_of (by push_cast; linarith) (by push_cast; linarith)
    rw [show 2 * 0 + 1 = 0 + 1 by rfl, A195538_z, A195538_z0, hf]
    rw [one_div]
    apply inv_eq_of_mul_eq_one_right
    push_cast
    linear_combination hs
  | succ k ih =>
    have e1 : A195538_z (2 * k + 2) = 2 + 2 * Real.sqrt 2 := by
      have hf : ⌊((Real.sqrt 2 + 1) / 2 : ℝ)⌋ = 1 :=
        A195538_floor_of (by push_cast; linarith) (by push_cast; linarith)
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, A195538_z, ih, hf]
      rw [one_div]
      apply inv_eq_of_mul_eq_one_right
      push_cast
      linear_combination hs
    have hf : ⌊(2 + 2 * Real.sqrt 2 : ℝ)⌋ = 4 :=
      A195538_floor_of (by push_cast; linarith) (by push_cast; linarith)
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, A195538_z, e1, hf]
    rw [one_div]
    apply inv_eq_of_mul_eq_one_right
    push_cast
    linear_combination hs

theorem A195538_c_val (k : ℕ) :
    A195538_c 0 = 5 ∧ A195538_c (2 * k + 1) = 1 ∧ A195538_c (2 * k + 2) = 4 := by
  obtain ⟨hl, hu⟩ := A195538_sqrt2_bounds
  have hs := A195538_sqrt2
  refine ⟨?_, ?_, ?_⟩
  · unfold A195538_c
    rw [A195538_z0]
    exact A195538_floor_of (by push_cast; linarith) (by push_cast; linarith)
  · unfold A195538_c
    rw [A195538_z_odd]
    exact A195538_floor_of (by push_cast; linarith) (by push_cast; linarith)
  · unfold A195538_c
    have hf : ⌊((Real.sqrt 2 + 1) / 2 : ℝ)⌋ = 1 :=
      A195538_floor_of (by push_cast; linarith) (by push_cast; linarith)
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, A195538_z, A195538_z_odd, hf]
    have e : 1 / ((Real.sqrt 2 + 1) / 2 - ((1 : ℤ) : ℝ)) = 2 + 2 * Real.sqrt 2 := by
      rw [one_div]
      apply inv_eq_of_mul_eq_one_right
      push_cast
      linear_combination hs
    rw [e]
    exact A195538_floor_of (by push_cast; linarith) (by push_cast; linarith)

/-! ### Convergents in terms of (X, W) -/

def A195538_U (k : ℕ) : ℤ := (A195538_X k : ℤ) + 2 * A195538_W k

def A195538_V (k : ℕ) : ℤ := (A195538_X k : ℤ) + 3 * A195538_W k

theorem A195538_U_succ (k : ℕ) : A195538_U (k + 1) = A195538_U k + 4 * A195538_V k := by
  unfold A195538_U A195538_V
  rw [A195538_X_succ, A195538_W_succ]
  push_cast
  ring

theorem A195538_V_succ (k : ℕ) : A195538_V (k + 1) = A195538_U k + 5 * A195538_V k := by
  unfold A195538_U A195538_V
  rw [A195538_X_succ, A195538_W_succ]
  push_cast
  ring

theorem A195538_U_step (k m : ℕ) (h : m = k + 1) :
    A195538_U m = A195538_U k + 4 * A195538_V k := by
  subst h
  exact A195538_U_succ k

theorem A195538_V_step (k m : ℕ) (h : m = k + 1) :
    A195538_V m = A195538_U k + 5 * A195538_V k := by
  subst h
  exact A195538_V_succ k

theorem A195538_UV_inv (k : ℕ) :
    A195538_U k ^ 2 + 4 * A195538_U k * A195538_V k - 4 * A195538_V k ^ 2 = 1 := by
  have h := A195538_inv k
  zify at h
  unfold A195538_U A195538_V
  linear_combination h

theorem A195538_U_pos (k : ℕ) : 0 < A195538_U k := by
  unfold A195538_U
  have := A195538_X_pos k
  omega

theorem A195538_V_pos (k : ℕ) : 0 < A195538_V k := by
  unfold A195538_V
  have := A195538_X_pos k
  omega

theorem A195538_P_succ_succ (n : ℕ) :
    A195538_P (n + 2) = A195538_c (n + 2) * A195538_P (n + 1) + A195538_P n := by
  rw [A195538_P]

theorem A195538_Q_succ_succ (n : ℕ) :
    A195538_Q (n + 2) = A195538_c (n + 2) * A195538_Q (n + 1) + A195538_Q n := by
  rw [A195538_Q]

theorem A195538_PQ (k : ℕ) :
    A195538_P (2 * k) = A195538_U (k + 1) ∧ A195538_P (2 * k + 1) = A195538_V (k + 1) ∧
    A195538_Q (2 * k) = A195538_U k ∧ A195538_Q (2 * k + 1) = A195538_V k := by
  induction k with
  | zero =>
    obtain ⟨h0, h1, -⟩ := A195538_c_val 0
    refine ⟨?_, ?_, rfl, ?_⟩
    · show A195538_c 0 = _
      rw [h0]
      decide
    · show A195538_c 1 * A195538_c 0 + 1 = _
      rw [h0, h1]
      decide
    · show A195538_c 1 = _
      rw [h1]
      decide
  | succ k ih =>
    obtain ⟨-, h1, h2⟩ := A195538_c_val k
    obtain ⟨-, h1', -⟩ := A195538_c_val (k + 1)
    obtain ⟨ihP0, ihP1, ihQ0, ihQ1⟩ := ih
    have eP0 : A195538_P (2 * (k + 1)) = A195538_U (k + 1 + 1) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, A195538_P_succ_succ, h2, ihP1, ihP0,
        A195538_U_succ (k + 1)]
      ring
    have eQ0 : A195538_Q (2 * (k + 1)) = A195538_U (k + 1) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, A195538_Q_succ_succ, h2, ihQ1, ihQ0,
        A195538_U_succ k]
      ring
    refine ⟨eP0, ?_, eQ0, ?_⟩
    · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, A195538_P_succ_succ,
        show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, h1',
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring, eP0, ihP1, A195538_V_succ (k + 1),
        A195538_U_succ (k + 1)]
      ring
    · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, A195538_Q_succ_succ,
        show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, h1',
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring, eQ0, ihQ1, A195538_V_succ k,
        A195538_U_succ k]
      ring

/-! ### Lowest terms -/

theorem A195538_den_eq {N D : ℤ} {p q : ℤ} (hD : 0 < D) (hc : IsCoprime N D)
    (he : ((p ^ 2 - q ^ 2 : ℤ) : ℚ) / ((2 * p * q : ℤ) : ℚ) = (N : ℚ) / (D : ℚ)) :
    ((((p ^ 2 - q ^ 2 : ℤ) : ℚ) / ((2 * p * q : ℤ) : ℚ)).den : ℤ) = D := by
  rw [he]
  exact Rat.den_div_eq_of_coprime hD (Int.isCoprime_iff_gcd_eq_one.mp hc)

theorem A195538_a_odd (k : ℕ) :
    (A195538_a (2 * k + 1) : ℤ) = (A195538_U k + 4 * A195538_V k) * A195538_U k := by
  obtain ⟨hP, -, hQ, -⟩ := A195538_PQ k
  have hI := A195538_UV_inv k
  have hU := A195538_U_pos k
  have hV := A195538_V_pos k
  unfold A195538_a A195538_frac
  rw [show 2 * k + 1 - 1 = 2 * k by omega, hP, hQ, A195538_U_succ]
  generalize A195538_U k = U at hI hU hV ⊢
  generalize A195538_V k = V at hI hU hV ⊢
  apply A195538_den_eq (N := 4 * V * (U + 2 * V)) (mul_pos (by linarith) hU)
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

theorem A195538_a_even (k : ℕ) :
    (A195538_a (2 * k + 2) : ℤ) = 2 * (A195538_U k + 5 * A195538_V k) * A195538_V k := by
  obtain ⟨-, hP, -, hQ⟩ := A195538_PQ k
  have hI := A195538_UV_inv k
  have hU := A195538_U_pos k
  have hV := A195538_V_pos k
  unfold A195538_a A195538_frac
  rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega, hP, hQ, A195538_V_succ]
  generalize A195538_U k = U at hI hU hV ⊢
  generalize A195538_V k = V at hI hU hV ⊢
  apply A195538_den_eq (N := (U + 4 * V) * (U + 6 * V))
    (mul_pos (mul_pos two_pos (by linarith)) hV)
  · have c1 : IsCoprime (U + 4 * V) 2 := ⟨U, -2 * V ^ 2, by linear_combination hI⟩
    have c2 : IsCoprime (U + 6 * V) 2 := ⟨U, -2 * V ^ 2 - U * V, by linear_combination hI⟩
    have c3 : IsCoprime (U + 4 * V) (U + 5 * V) := ⟨U + 4 * V, -4 * V, by linear_combination hI⟩
    have c4 : IsCoprime (U + 6 * V) (U + 5 * V) := ⟨U + 6 * V, -8 * V, by linear_combination hI⟩
    have c5 : IsCoprime (U + 4 * V) V := ⟨U, -4 * V, by linear_combination hI⟩
    have c6 : IsCoprime (U + 6 * V) V := ⟨U, -2 * U - 4 * V, by linear_combination hI⟩
    exact IsCoprime.mul_left (IsCoprime.mul_right (IsCoprime.mul_right c1 c3) c5)
      (IsCoprime.mul_right (IsCoprime.mul_right c2 c4) c6)
  · have hUq : (0 : ℚ) < U := by exact_mod_cast hU
    have hVq : (0 : ℚ) < V := by exact_mod_cast hV
    push_cast
    rw [div_eq_div_iff (mul_pos (mul_pos two_pos (by linarith)) hVq).ne'
      (mul_pos (mul_pos two_pos (by linarith)) hVq).ne']
    ring

/-! ### Data and recurrence -/

/-- Closed form of a(n) on ℕ (computable). -/
def A195538_af (n : ℕ) : ℕ :=
  if n % 2 = 1 then
    (5 * A195538_X (n / 2) + 14 * A195538_W (n / 2)) * (A195538_X (n / 2) + 2 * A195538_W (n / 2))
  else
    2 * (6 * A195538_X (n / 2 - 1) + 17 * A195538_W (n / 2 - 1)) *
      (A195538_X (n / 2 - 1) + 3 * A195538_W (n / 2 - 1))

theorem A195538_a_eq_af (n : ℕ) (hn : 1 ≤ n) : A195538_a n = A195538_af n := by
  zify
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain rfl : n = 2 * j + 2 := by omega
    rw [A195538_a_even]
    unfold A195538_af A195538_U A195538_V
    rw [ite_eq_right (by omega), show (2 * j + 2) / 2 - 1 = j by omega]
    push_cast
    ring
  · subst hk
    rw [A195538_a_odd]
    unfold A195538_af A195538_U A195538_V
    rw [ite_eq_left (by omega), show (2 * k + 1) / 2 = k by omega]
    push_cast
    ring

theorem A195538_data :
    (List.range 16).map (fun i => A195538_a (i + 1)) =
      [5, 12, 145, 420, 4901, 14280, 166465, 485112, 5654885, 16479540, 192099601,
       559819260, 6525731525, 19017375312, 221682772225, 646030941360] := by
  rw [List.map_congr_left (g := fun i => A195538_af (i + 1))
    (fun i _ => A195538_a_eq_af (i + 1) (by omega))]
  decide

theorem A195538_rec (n : ℕ) (hn : 7 ≤ n) :
    (A195538_a n : ℤ) = 35 * A195538_a (n - 2) - 35 * A195538_a (n - 4) + A195538_a (n - 6) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    obtain rfl : n = 2 * (j + 3) + 2 := by omega
    rw [show 2 * (j + 3) + 2 - 2 = 2 * (j + 2) + 2 by omega,
      show 2 * (j + 3) + 2 - 4 = 2 * (j + 1) + 2 by omega,
      show 2 * (j + 3) + 2 - 6 = 2 * j + 2 by omega,
      A195538_a_even, A195538_a_even, A195538_a_even, A195538_a_even,
      A195538_U_step (j + 2) (j + 3) rfl, A195538_V_step (j + 2) (j + 3) rfl,
      A195538_U_step (j + 1) (j + 2) rfl, A195538_V_step (j + 1) (j + 2) rfl,
      A195538_U_step j (j + 1) rfl, A195538_V_step j (j + 1) rfl]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    subst hk
    rw [show 2 * (j + 3) + 1 - 2 = 2 * (j + 2) + 1 by omega,
      show 2 * (j + 3) + 1 - 4 = 2 * (j + 1) + 1 by omega,
      show 2 * (j + 3) + 1 - 6 = 2 * j + 1 by omega,
      A195538_a_odd, A195538_a_odd, A195538_a_odd, A195538_a_odd,
      A195538_U_step (j + 2) (j + 3) rfl, A195538_V_step (j + 2) (j + 3) rfl,
      A195538_U_step (j + 1) (j + 2) rfl, A195538_V_step (j + 1) (j + 2) rfl,
      A195538_U_step j (j + 1) rfl, A195538_V_step j (j + 1) rfl]
    ring

/-! ### Bisection A076218 -/

/-- m such that 2m^2 - 3m + 1 is a square. -/
def A195538_S1 (m : ℕ) : Prop := ∃ t : ℕ, (2 * (m : ℤ) ^ 2 - 3 * m + 1) = (t : ℤ) ^ 2

/-- A076218 (offset 1): the n-th such number. -/
noncomputable def A076218 (n : ℕ) : ℕ := Nat.nth A195538_S1 (n - 1)

/-- Enumeration of S1: 0, then 4 W_k^2 + 1. -/
def A195538_f1 : ℕ → ℕ
  | 0 => 0
  | k + 1 => 4 * A195538_W k ^ 2 + 1

theorem A195538_f1_mono : StrictMono A195538_f1 := by
  apply strictMono_nat_of_lt_succ
  intro k
  cases k with
  | zero => simp [A195538_f1]
  | succ k =>
    simp only [A195538_f1]
    have := A195538_W_lt k
    have : A195538_W k ^ 2 < A195538_W (k + 1) ^ 2 := Nat.pow_lt_pow_left this (by norm_num)
    omega

theorem A195538_S1_iff (m : ℕ) : A195538_S1 m ↔ ∃ k, A195538_f1 k = m := by
  constructor
  · rintro ⟨t, ht⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, rfl⟩
    -- (2m - 1)(m - 1) = t^2 with coprime factors.
    --
    have hprod : (2 * m - 1) * (m - 1) = t ^ 2 := by
      zify [show 1 ≤ 2 * m by omega, show 1 ≤ m from hm]
      linear_combination ht
    have hcop : Nat.Coprime (2 * m - 1) (m - 1) := by
      rw [show 2 * m - 1 = (m - 1) * 2 + 1 by omega]
      simp
    obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) hprod
    obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm)
      ((mul_comm _ _).trans hprod)
    have hvu : v ^ 2 = 2 * u ^ 2 + 1 := by omega
    -- u is even: v is odd, v = 2s + 1, so u^2 = 2s(s+1).
    --
    have hue : Even u := by
      have hvo : Odd v := by
        rcases Nat.even_or_odd v with he | ho
        · exfalso
          obtain ⟨s, rfl⟩ := he
          ring_nf at hvu
          omega
        · exact ho
      obtain ⟨s, rfl⟩ := hvo
      have : u ^ 2 = 2 * (s * (s + 1)) := by nlinarith
      exact (Nat.even_pow' (n := 2) (by norm_num)).mp ⟨s * (s + 1), by omega⟩
    obtain ⟨w, rfl⟩ := hue
    obtain ⟨k, hk1, hk2⟩ := A195538_classify w v (by nlinarith)
    refine ⟨k + 1, ?_⟩
    simp only [A195538_f1, hk2]
    have : m = (w + w) ^ 2 + 1 := by omega
    rw [this]
    ring
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => exact ⟨1, by simp [A195538_f1]⟩
    | succ k =>
      refine ⟨2 * A195538_X k * A195538_W k, ?_⟩
      have h := A195538_inv k
      zify at h
      simp only [A195538_f1]
      push_cast
      linear_combination -4 * (A195538_W k : ℤ) ^ 2 * h

/-! ### Bisection A098602 = A001652 · A046090 -/

/-- A001652: x(n) = 6 x(n-1) - x(n-2) + 2, x(0) = 0, x(1) = 3. -/
def A001652 : ℕ → ℤ
  | 0 => 0
  | 1 => 3
  | n + 2 => 6 * A001652 (n + 1) - A001652 n + 2

/-- X + 1 over Pythagorean triples (X, X+1, Z). -/
def A195538_S2 (m : ℕ) : Prop := 1 ≤ m ∧ ∃ z : ℕ, (m - 1) ^ 2 + m ^ 2 = z ^ 2

/-- A046090 (offset 0). -/
noncomputable def A046090 (n : ℕ) : ℕ := Nat.nth A195538_S2 n

noncomputable def A098602 (n : ℕ) : ℤ := A001652 n * A046090 n

def A195538_f2 (k : ℕ) : ℕ := (A195538_X k + 4 * A195538_W k + 1) / 2

theorem A195538_two_f2 (k : ℕ) : 2 * A195538_f2 k = A195538_X k + 4 * A195538_W k + 1 := by
  unfold A195538_f2
  have := A195538_X_odd k
  omega

theorem A195538_f2_mono : StrictMono A195538_f2 := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 := A195538_two_f2 k
  have h2 := A195538_two_f2 (k + 1)
  have := A195538_XW_lt k
  omega

theorem A195538_S2_iff (m : ℕ) : A195538_S2 m ↔ ∃ k, A195538_f2 k = m := by
  constructor
  · rintro ⟨hm, z, hz⟩
    -- z is odd: z^2 = 2m^2 - 2m + 1.
    --
    have hzo : Odd z := by
      rcases Nat.even_or_odd z with ⟨r, rfl⟩ | ho
      · exfalso
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hz
        ring_nf at hz
        omega
      · exact ho
    obtain ⟨r, rfl⟩ := hzo
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hz
    have h1 : r ≤ m' := by nlinarith
    have h2 : 2 * (m' + 1) ≤ 4 * r + 3 := by nlinarith
    obtain ⟨k, hk1, hk2⟩ := A195538_classify (m' - r) (4 * r + 3 - 2 * (m' + 1)) (by
      zify [h1, h2]
      zify at hz
      linear_combination -2 * hz)
    refine ⟨k, ?_⟩
    have := A195538_two_f2 k
    omega
  · rintro ⟨k, rfl⟩
    have h2 := A195538_two_f2 k
    have hI := A195538_inv k
    refine ⟨by omega, A195538_X k + 2 * A195538_W k, ?_⟩
    have hge : 1 ≤ A195538_f2 k := by omega
    zify [hge] at h2 hI ⊢
    have : 2 * (((A195538_f2 k : ℤ) - 1) ^ 2 + (A195538_f2 k : ℤ) ^ 2) =
        2 * ((A195538_X k : ℤ) + 2 * A195538_W k) ^ 2 := by
      linear_combination (2 * (A195538_f2 k : ℤ) - 1 + (A195538_X k + 4 * A195538_W k)) * h2 - hI
    linarith

theorem A195538_A001652 (k : ℕ) :
    2 * A001652 k + 1 = (A195538_X k : ℤ) + 4 * A195538_W k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | k + 2, ih =>
      have e0 := ih k (by omega)
      have e1 := ih (k + 1) (by omega)
      have hX2 : A195538_X (k + 2) = 3 * (3 * A195538_X k + 8 * A195538_W k) +
          8 * (A195538_X k + 3 * A195538_W k) := rfl
      have hW2 : A195538_W (k + 2) = (3 * A195538_X k + 8 * A195538_W k) +
          3 * (A195538_X k + 3 * A195538_W k) := rfl
      rw [A001652, hX2, hW2]
      rw [A195538_X_succ, A195538_W_succ] at e1
      push_cast at e1 ⊢
      linear_combination 6 * e1 - e0

/-! ### Main theorem -/

theorem A195538_main :
    (List.range 16).map (fun i => A195538_a (i + 1)) =
      [5, 12, 145, 420, 4901, 14280, 166465, 485112, 5654885, 16479540, 192099601,
       559819260, 6525731525, 19017375312, 221682772225, 646030941360] ∧
    (∀ n, 7 ≤ n →
      (A195538_a n : ℤ) = 35 * A195538_a (n - 2) - 35 * A195538_a (n - 4) + A195538_a (n - 6)) ∧
    (∀ k, 1 ≤ k → (A195538_a (2 * k) : ℤ) = A098602 k) ∧
    (∀ k, 1 ≤ k → A195538_a (2 * k - 1) = A076218 (k + 2)) := by
  refine ⟨A195538_data, A195538_rec, ?_, ?_⟩
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    unfold A098602 A046090
    rw [A195538_nth_eq A195538_f2_mono A195538_S2_iff, show 2 * (j + 1) = 2 * j + 2 by ring,
      A195538_a_even]
    have h1 := A195538_A001652 (j + 1)
    have h2 := A195538_two_f2 (j + 1)
    have hI := A195538_inv j
    zify at h2 hI
    rw [A195538_X_succ, A195538_W_succ] at h1 h2
    push_cast at h1 h2
    unfold A195538_U A195538_V
    generalize (A195538_X j : ℤ) = X at h1 h2 hI ⊢
    generalize (A195538_W j : ℤ) = W at h1 h2 hI ⊢
    generalize A001652 (j + 1) = x at h1 h2 ⊢
    generalize (A195538_f2 (j + 1) : ℤ) = f at h1 h2 ⊢
    have : 4 * (2 * ((X + 2 * W) + 5 * (X + 3 * W)) * (X + 3 * W)) = 4 * (x * f) := by
      linear_combination (-(7 * X + 20 * W + 1)) * h1 - 2 * x * h2 - hI
    linarith
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    unfold A076218
    rw [show j + 1 + 2 - 1 = (j + 1) + 1 by omega, A195538_nth_eq A195538_f1_mono A195538_S1_iff,
      show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    zify
    rw [A195538_a_odd]
    simp only [A195538_f1]
    have hI := A195538_inv j
    zify at hI
    rw [A195538_W_succ]
    unfold A195538_U A195538_V
    push_cast
    linear_combination hI
