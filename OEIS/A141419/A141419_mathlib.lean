/-
OEIS A141419: T(n, k) = A000217(n) - A000217(n - k), 1 <= k <= n.
Conjecture (L. Edson Jeffery, 2012): with N = 2n+1, t(n, k) is the k-th diagonal entry of
S_N^T S_N, i.e. t(n, k) = Sum_{m=1..n} U_{k-1}(cos((2m-1) pi / N))^2, U = Chebyshev polynomials of
the second kind.

Checked here (Mathlib): `A141419_conjecture`: for 1 <= k <= n,
Sum_{m < n} (U_{k-1}(cos((2m+1) pi / (2n+1))))^2 = A141419 n k, with `Polynomial.Chebyshev.U` and
A141419 n k = n(n+1)/2 - (n-k)(n-k+1)/2 (natural-number division, as in the OEIS definition).
The remark in the same comment about A057059 (X_N as a combination of unit-primitive matrices)
is not treated. Nothing else is outside Lean.
-/
import Mathlib

open Real Finset

def A141419 (n k : ℕ) : ℕ := n * (n + 1) / 2 - (n - k) * (n - k + 1) / 2

/-- Telescoping: 2 sin a * Sum_{m<n} cos((2m+1)a) = sin(2na). -/
lemma A141419_tele (a : ℝ) (n : ℕ) :
    2 * sin a * ∑ m ∈ range n, cos ((2 * m + 1) * a) = sin (2 * n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    have h1 : (2 * ((n : ℝ) + 1)) * a = (2 * n * a + a) + a := by ring
    have h2 : (2 * (n : ℝ) + 1) * a = 2 * n * a + a := by ring
    rw [h1, h2, sin_add (2 * n * a + a), sin_add (2 * n * a), cos_add (2 * n * a)]
    have := sin_sq_add_cos_sq a
    linear_combination (-sin (2 * n * a)) * this

lemma A141419_cos_sum (n l : ℕ) (hl1 : 1 ≤ l) (hl : l < 2 * n + 1) :
    ∑ m ∈ range n, cos ((2 * m + 1) * (2 * l * π / (2 * n + 1))) = -1 / 2 := by
  set a := 2 * l * π / (2 * n + 1) with ha
  have hN : (0 : ℝ) < 2 * n + 1 := by positivity
  have hsa : sin a ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.1 h
    rw [ha] at hj
    have hj' : (j : ℝ) * (2 * n + 1) = 2 * l := by
      field_simp at hj
      nlinarith [pi_pos]
    have hj'' : j * (2 * (n : ℤ) + 1) = 2 * l := by exact_mod_cast hj'
    have h1 : 1 ≤ j := by nlinarith
    have h2 : j ≤ 1 := by nlinarith
    have : j = 1 := le_antisymm h2 h1
    subst this
    omega
  have hsin : sin (2 * n * a) = - sin a := by
    have : 2 * n * a = 2 * l * π - a := by
      rw [ha]; field_simp; ring
    rw [this, sin_sub]
    have hs : sin (2 * l * π) = 0 := by
      have := Real.sin_nat_mul_pi (2 * l); push_cast at this; exact this
    have hc : cos (2 * l * π) = 1 := by
      have := Real.cos_nat_mul_two_pi l
      rw [show (l : ℝ) * (2 * π) = 2 * l * π by ring] at this; exact this
    rw [hs, hc]; ring
  have := A141419_tele a n
  rw [hsin] at this
  have h2 : 2 * sin a ≠ 0 := mul_ne_zero two_ne_zero hsa
  field_simp
  linarith [this, show 2 * sin a * (∑ m ∈ range n, cos ((2 * m + 1) * a)) =
    sin a * (2 * ∑ m ∈ range n, cos ((2 * m + 1) * a)) by ring, mul_left_cancel₀ hsa
    (show sin a * (2 * ∑ m ∈ range n, cos ((2 * m + 1) * a)) = sin a * (-1) by linarith)]

lemma A141419_trig (u t : ℝ) :
    sin (u + t) ^ 2 - 2 * sin u ^ 2 + sin (u - t) ^ 2 = 2 * cos (2 * u) * sin t ^ 2 := by
  rw [sin_add, sin_sub, cos_two_mul]
  have ht := sin_sq_add_cos_sq t
  have hu := sin_sq_add_cos_sq u
  linear_combination (2 * sin u ^ 2) * ht - (2 * sin t ^ 2) * hu

/-- g(k) = Sum_m sin(k θ_m)^2 / sin(θ_m)^2. -/
noncomputable def A141419g (n k : ℕ) : ℝ :=
  ∑ m ∈ range n, sin (k * ((2 * m + 1) * π / (2 * n + 1))) ^ 2 /
    sin ((2 * m + 1) * π / (2 * n + 1)) ^ 2

lemma A141419_sin_ne (n m : ℕ) (hm : m < n) : sin ((2 * m + 1) * π / (2 * n + 1)) ≠ 0 := by
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm
    nlinarith [pi_pos]

lemma A141419_rec (n k : ℕ) (hk : k + 1 < 2 * n + 1) :
    A141419g n (k + 2) - 2 * A141419g n (k + 1) + A141419g n k = -1 := by
  have key : ∀ m ∈ range n,
      sin (((k + 2 : ℕ) : ℝ) * ((2 * m + 1) * π / (2 * n + 1))) ^ 2 /
          sin ((2 * m + 1) * π / (2 * n + 1)) ^ 2
        - 2 * (sin (((k + 1 : ℕ) : ℝ) * ((2 * m + 1) * π / (2 * n + 1))) ^ 2 /
          sin ((2 * m + 1) * π / (2 * n + 1)) ^ 2)
        + sin ((k : ℝ) * ((2 * m + 1) * π / (2 * n + 1))) ^ 2 /
          sin ((2 * m + 1) * π / (2 * n + 1)) ^ 2
        = 2 * cos ((2 * m + 1) * (2 * ((k + 1 : ℕ) : ℝ) * π / (2 * n + 1))) := by
    intro m hm
    have hs := A141419_sin_ne n m (mem_range.1 hm)
    set t := (2 * m + 1) * π / (2 * n + 1)
    have := A141419_trig (((k + 1 : ℕ) : ℝ) * t) t
    have e1 : ((k + 1 : ℕ) : ℝ) * t + t = ((k + 2 : ℕ) : ℝ) * t := by push_cast; ring
    have e2 : ((k + 1 : ℕ) : ℝ) * t - t = (k : ℝ) * t := by push_cast; ring
    have e3 : (2 * m + 1) * (2 * ((k + 1 : ℕ) : ℝ) * π / (2 * n + 1)) =
        2 * (((k + 1 : ℕ) : ℝ) * t) := by simp only [t]; ring
    rw [e1, e2] at this
    rw [e3, show ∀ x y z w : ℝ, x / w - 2 * (y / w) + z / w = (x - 2 * y + z) / w from
      fun x y z w => by ring, this, mul_div_assoc, div_self (pow_ne_zero 2 hs), mul_one]
  unfold A141419g
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib, sum_congr rfl key, ← mul_sum,
    A141419_cos_sum n (k + 1) (by omega) hk]
  norm_num

lemma A141419_g0 (n : ℕ) : A141419g n 0 = 0 := by simp [A141419g]

lemma A141419_g1 (n : ℕ) : A141419g n 1 = n := by
  unfold A141419g
  rw [sum_congr rfl (fun m hm => by
    rw [Nat.cast_one, one_mul, div_self (pow_ne_zero 2 (A141419_sin_ne n m (mem_range.1 hm)))])]
  simp

lemma A141419_closed (n : ℕ) : ∀ k, k ≤ 2 * n →
    A141419g n k = n * k - k * (k - 1) / 2 ∧
    (k + 1 ≤ 2 * n → A141419g n (k + 1) = n * (k + 1) - (k + 1) * k / 2) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [A141419_g0], fun _ => by rw [A141419_g1]; push_cast; ring⟩
  | succ k ih =>
    intro hk
    obtain ⟨-, h1⟩ := ih (by omega)
    have h1 := h1 hk
    refine ⟨by rw [h1]; push_cast; ring, fun hk2 => ?_⟩
    obtain ⟨h0, -⟩ := ih (by omega)
    have hr : A141419g n (k + 1 + 1) - 2 * A141419g n (k + 1) + A141419g n k = -1 :=
      A141419_rec n k (by omega)
    push_cast at h1 h0 ⊢
    linarith

/-- Main theorem: the diagonal entries of S_N^T S_N are the rows of A141419. -/
theorem A141419_conjecture (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∑ m ∈ range n,
      ((Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (cos ((2 * m + 1) * π / (2 * n + 1)))) ^ 2 =
      (A141419 n k : ℝ) := by
  have hU : ∀ m ∈ range n,
      ((Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (cos ((2 * m + 1) * π / (2 * n + 1)))) ^ 2 =
        sin (k * ((2 * m + 1) * π / (2 * n + 1))) ^ 2 /
          sin ((2 * m + 1) * π / (2 * n + 1)) ^ 2 := by
    intro m hm
    have hs := A141419_sin_ne n m (mem_range.1 hm)
    have := Polynomial.Chebyshev.U_real_cos ((2 * m + 1) * π / (2 * n + 1)) ((k : ℤ) - 1)
    push_cast at this
    rw [show ((k : ℝ) - 1 + 1) = k by ring] at this
    rw [← this]
    field_simp
  rw [sum_congr rfl hU]
  have := (A141419_closed n k (by omega)).1
  unfold A141419g at this
  rw [this]
  -- the OEIS value
  obtain ⟨j, rfl⟩ : ∃ j, n = j + k := ⟨n - k, by omega⟩
  have hj : j + k - k = j := by omega
  unfold A141419
  rw [hj]
  have e1 : 2 ∣ (j + k) * (j + k + 1) := (Nat.even_mul_succ_self _).two_dvd
  have e2 : 2 ∣ j * (j + 1) := (Nat.even_mul_succ_self _).two_dvd
  have hle : j * (j + 1) / 2 ≤ (j + k) * (j + k + 1) / 2 :=
    Nat.div_le_div_right (by nlinarith)
  rw [Nat.cast_sub hle, Nat.cast_div e1 (by norm_num), Nat.cast_div e2 (by norm_num)]
  push_cast
  ring
