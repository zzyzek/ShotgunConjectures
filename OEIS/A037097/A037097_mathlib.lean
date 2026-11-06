import Mathlib

/-
OEIS A037097, A037096, A036284 (A. Karttunen): periodic vertical binary vectors.
Read as GF(2)[X] polynomials (binary digit k of a(n) = coefficient of X^k):
  A037097(n) = sum_{k < 2^(n-1)} bit_n(3^k) X^k,   A037096(n) = sum_{k < 2^n} bit_n(3^k) X^k,
  A036284(n) = sum_{k < 3*2^n} bit_n(F_k) X^k,      bit_n(v) = floor(v / 2^n) mod 2.
`colPoly f n N` is sum_{k<N} C(bit_n(f k)) X^k.

Main theorems.
* `A037097_dvd`: n ≥ 3 → A037097poly n = (X+1)^(2^(n-2) - 1) * R with R(1) = 1
  (the comment as corrected by Q. Gu, Jul 2026: exponent A000225(n-2); exact power).
* `A037096_dvd`: n ≥ 3 → (X+1)^(3*2^(n-2) - 1) ∣ A037096poly n  (A055010(n-1) = 3*2^(n-2) - 1).
* `A036284_dvd`: n ≥ 1 → (X^3+1)^(2^(n-1) - 1) * (X+1) ∣ A036284poly n  (both conjectures).
* `A037097_old_exponent_false`: the older exponent 2^(n-1) - 1 fails at n = 3.
Route.  `flip3`: 3^(2^(n-2)) = 1 + 2^n * odd, so bit n of 3^k flips after 2^(n-2) steps;
`flipF`: for L = 3*2^(n-1), n ≥ 2, F_L = 2^(n+1) * odd and F_(L-1) = 1 + 2^n (mod 2^(n+1)),
so bit n of F_k flips after L steps exactly when F_k is odd (3 ∤ k).  `colPoly_double` turns
a flip pattern c into Q = A (1 + X^M) + X^M sum c_k X^k; in characteristic 2,
1 + X^(2^j) = (X+1)^(2^j) and sum_{k<2^j} Y^k = (Y+1)^(2^j - 1) (`geom_eq`, `geom3`).
Not checked here: the reading of "a(n) considered as a GF(2)[X]-polynomial".
-/

open Polynomial Finset

namespace A037097

/-- The GF(2) polynomial with coefficient bit n of f k at X^k, k < N. -/
noncomputable def colPoly (f : ℕ → ℕ) (n N : ℕ) : (ZMod 2)[X] :=
  ∑ k ∈ range N, C ((f k / 2 ^ n : ℕ) : ZMod 2) * X ^ k

/-- Splitting a sum over two consecutive blocks of length M. -/
lemma colPoly_double (f : ℕ → ℕ) (n M : ℕ) (c : ℕ → ZMod 2)
    (hflip : ∀ k, ((f (k + M) / 2 ^ n : ℕ) : ZMod 2) = ((f k / 2 ^ n : ℕ) : ZMod 2) + c k) :
    colPoly f n (M + M) = colPoly f n M * (1 + X ^ M) + X ^ M * ∑ k ∈ range M, C (c k) * X ^ k := by
  unfold colPoly
  rw [sum_range_add]
  have : ∀ k, C ((f (M + k) / 2 ^ n : ℕ) : ZMod 2) * X ^ (M + k) =
      X ^ M * (C ((f k / 2 ^ n : ℕ) : ZMod 2) * X ^ k) + X ^ M * (C (c k) * X ^ k) := by
    intro k; rw [add_comm M k, hflip, C_add, pow_add]; ring
  simp_rw [this, sum_add_distrib, ← mul_sum]
  ring

/-- In characteristic 2, 1 + X^(2^j) = (X + 1)^(2^j). -/
lemma one_add_X_pow (j : ℕ) : (1 + X ^ (2 ^ j) : (ZMod 2)[X]) = (X + 1) ^ (2 ^ j) := by
  rw [add_pow_char_pow (p := 2), one_pow, add_comm]

/-- Over GF(2), sum_{k < 2^j} X^k = (X + 1)^(2^j - 1). -/
lemma geom_eq (j : ℕ) : (∑ k ∈ range (2 ^ j), (X : (ZMod 2)[X]) ^ k) = (X + 1) ^ (2 ^ j - 1) := by
  have h1 : (∑ k ∈ range (2 ^ j), (X : (ZMod 2)[X]) ^ k) * (X - 1) = X ^ (2 ^ j) - 1 := geom_sum_mul _ _
  have h2 : (X : (ZMod 2)[X]) - 1 = X + 1 := CharTwo.sub_eq_add _ _
  have h3 : (X : (ZMod 2)[X]) ^ (2 ^ j) - 1 = (X + 1) ^ (2 ^ j) := by
    rw [CharTwo.sub_eq_add, add_comm, one_add_X_pow]
  rw [h2, h3] at h1
  have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hne : (X + 1 : (ZMod 2)[X]) ≠ 0 := X_add_C_ne_zero 1
  apply mul_right_cancel₀ hne
  rw [h1, ← pow_succ, Nat.sub_add_cancel hpos]

lemma cast_odd {m : ℕ} (h : Odd m) : ((m : ℕ) : ZMod 2) = 1 := by
  rw [← ZMod.natCast_mod, Nat.odd_iff.mp h, Nat.cast_one]

/-- 3^(2^(j+1)) = 1 + 2^(j+3) * (odd). -/
lemma three_pow (j : ℕ) : ∃ u, 3 ^ (2 ^ (j + 1)) = 1 + 2 ^ (j + 3) * (2 * u + 1) := by
  induction j with
  | zero => exact ⟨0, by norm_num⟩
  | succ j ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨u + 2 ^ (j + 1) * (2 * u + 1) ^ 2, ?_⟩
    rw [pow_succ 2 (j + 1), pow_mul, hu]
    ring

/-- Bit n of 3^k flips after M = 2^(n-2) steps (n = j + 3). -/
lemma flip3 (j k : ℕ) :
    ((3 ^ (k + 2 ^ (j + 1)) / 2 ^ (j + 3) : ℕ) : ZMod 2) = ((3 ^ k / 2 ^ (j + 3) : ℕ) : ZMod 2) + 1 := by
  obtain ⟨u, hu⟩ := three_pow j
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨r, hr⟩ := hodd
  have e : 3 ^ (k + 2 ^ (j + 1)) = 3 ^ k + 2 ^ (j + 3) * (3 ^ k * (2 * u + 1)) := by
    rw [pow_add, hu]; ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.cast_add,
    cast_odd (Odd.mul (Odd.pow (by decide)) (odd_two_mul_add_one u))]

end A037097

open A037097

/-- OEIS A037097(n) as a GF(2)[X] polynomial: sum_{k < 2^(n-1)} bit_n(3^k) X^k. -/
noncomputable def A037097poly (n : ℕ) : (ZMod 2)[X] := colPoly (fun k => 3 ^ k) n (2 ^ (n - 1))

/-- OEIS A037096(n) as a GF(2)[X] polynomial: sum_{k < 2^n} bit_n(3^k) X^k. -/
noncomputable def A037096poly (n : ℕ) : (ZMod 2)[X] := colPoly (fun k => 3 ^ k) n (2 ^ n)

/-- Corrected conjecture of A037097 (Gu 2026): for n ≥ 3, (X+1)^(2^(n-2) - 1) divides a(n);
the cofactor is not divisible by X + 1. -/
theorem A037097_dvd (n : ℕ) (hn : 3 ≤ n) :
    ∃ R : (ZMod 2)[X], A037097poly n = (X + 1) ^ (2 ^ (n - 2) - 1) * R ∧ R.eval 1 = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have hM : 2 ^ (j + 3 - 1) = 2 ^ (j + 1) + 2 ^ (j + 1) := by
    rw [show j + 3 - 1 = (j + 1) + 1 by omega, pow_succ]; ring
  have hsplit := colPoly_double (fun k => 3 ^ k) (j + 3) (2 ^ (j + 1)) (fun _ => 1) (flip3 j)
  simp only [C_1, one_mul] at hsplit
  rw [geom_eq, one_add_X_pow] at hsplit
  set A := colPoly (fun k => 3 ^ k) (j + 3) (2 ^ (j + 1))
  refine ⟨A * (X + 1) + X ^ (2 ^ (j + 1)), ?_, ?_⟩
  · unfold A037097poly
    rw [hM, hsplit, show j + 3 - 2 = j + 1 by omega]
    have hpos : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    rw [show ((X : (ZMod 2)[X]) + 1) ^ (2 ^ (j + 1)) = (X + 1) ^ (2 ^ (j + 1) - 1) * (X + 1) by
      rw [← pow_succ, Nat.sub_add_cancel hpos]]
    ring
  · simp only [eval_add, eval_mul, eval_pow, eval_X, eval_one]
    have : (1 + 1 : ZMod 2) = 0 := by decide
    simp [this]

/-- Conjecture of A037096: for n ≥ 3, (X+1)^(A055010(n-1)) = (X+1)^(3*2^(n-2) - 1) divides a(n). -/
theorem A037096_dvd (n : ℕ) (hn : 3 ≤ n) :
    (X + 1) ^ (3 * 2 ^ (n - 2) - 1) ∣ A037096poly n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  obtain ⟨R, hR, -⟩ := A037097_dvd (j + 3) hn
  rw [show j + 3 - 2 = j + 1 by omega] at hR
  -- bit n of 3^k has period 2^(n-1)
  have hper : ∀ k, ((3 ^ (k + 2 ^ (j + 2)) / 2 ^ (j + 3) : ℕ) : ZMod 2) =
      ((3 ^ k / 2 ^ (j + 3) : ℕ) : ZMod 2) + 0 := by
    intro k
    have h1 := flip3 j k
    have h2 := flip3 j (k + 2 ^ (j + 1))
    rw [show k + 2 ^ (j + 1) + 2 ^ (j + 1) = k + 2 ^ (j + 2) by rw [pow_succ 2 (j+1)]; ring] at h2
    rw [h2, h1, add_zero, add_assoc]
    have : (1 + 1 : ZMod 2) = 0 := by decide
    rw [this, add_zero]
  have hsplit := colPoly_double (fun k => 3 ^ k) (j + 3) (2 ^ (j + 2)) (fun _ => 0) hper
  simp only [C_0, zero_mul, sum_const_zero, mul_zero, add_zero] at hsplit
  unfold A037096poly
  rw [show 2 ^ (j + 3) = 2 ^ (j + 2) + 2 ^ (j + 2) by rw [pow_succ 2 (j + 2)]; ring, hsplit,
    one_add_X_pow]
  have h97 : colPoly (fun k => 3 ^ k) (j + 3) (2 ^ (j + 2)) = (X + 1) ^ (2 ^ (j + 1) - 1) * R := by
    rw [← hR]; unfold A037097poly; rw [show j + 3 - 1 = j + 2 by omega]
  rw [h97, show j + 3 - 2 = j + 1 by omega]
  refine ⟨R, ?_⟩
  have hpos : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  rw [show 3 * 2 ^ (j + 1) - 1 = (2 ^ (j + 1) - 1) + 2 ^ (j + 2) by rw [pow_succ 2 (j + 1)]; omega]
  ring

namespace A037097

/-- In characteristic 2, 1 + Y^(2^j) = (Y + 1)^(2^j). -/
lemma one_add_pow_two_pow (Y : (ZMod 2)[X]) (j : ℕ) : 1 + Y ^ (2 ^ j) = (Y + 1) ^ (2 ^ j) := by
  rw [add_pow_char_pow (p := 2), one_pow, add_comm]

/-- Over GF(2), sum_{j < 2^i} Y^j = (Y + 1)^(2^i - 1) for Y ≠ -1, here Y = X^3. -/
lemma geom3 (i : ℕ) :
    (∑ k ∈ range (2 ^ i), ((X : (ZMod 2)[X]) ^ 3) ^ k) = (X ^ 3 + 1) ^ (2 ^ i - 1) := by
  have h1 := geom_sum_mul ((X : (ZMod 2)[X]) ^ 3) (2 ^ i)
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm (_ ^ (2 ^ i)) 1, one_add_pow_two_pow] at h1
  have hne : ((X : (ZMod 2)[X]) ^ 3 + 1) ≠ 0 := by
    intro h
    have := congrArg (fun p => p.natDegree) h
    simp at this
  apply mul_right_cancel₀ hne
  rw [h1, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]

lemma fib_cast_add_three (k : ℕ) : ((Nat.fib (k + 3) : ℕ) : ZMod 2) = (Nat.fib k : ZMod 2) := by
  have : Nat.fib (k + 3) = Nat.fib k + 2 * Nat.fib (k + 1) := by
    rw [Nat.fib_add_two, Nat.fib_add_two (n := k)]; ring
  rw [this]; push_cast
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul, add_zero]

lemma fib_cast_mod3 (j : ℕ) : ((Nat.fib (3 * j) : ℕ) : ZMod 2) = 0 ∧
    ((Nat.fib (3 * j + 1) : ℕ) : ZMod 2) = 1 ∧ ((Nat.fib (3 * j + 2) : ℕ) : ZMod 2) = 1 := by
  induction j with
  | zero => simp [Nat.fib_add_two]
  | succ j ih =>
    rw [show 3 * (j + 1) = 3 * j + 3 by ring, show 3 * j + 3 + 1 = (3 * j + 1) + 3 by ring,
      show 3 * j + 3 + 2 = (3 * j + 2) + 3 by ring, fib_cast_add_three, fib_cast_add_three,
      fib_cast_add_three]
    exact ih

/-- Sum of (F_k mod 2) X^k over k < 3N equals (X + X^2) sum_{j<N} X^(3j). -/
lemma fib_parity_sum (N : ℕ) :
    (∑ k ∈ range (3 * N), C ((Nat.fib k : ℕ) : ZMod 2) * X ^ k) =
      (X + X ^ 2) * ∑ j ∈ range N, ((X : (ZMod 2)[X]) ^ 3) ^ j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ,
      show 3 * N + 1 + 1 = 3 * N + 2 by ring, ih, sum_range_succ]
    obtain ⟨h0, h1, h2⟩ := fib_cast_mod3 N
    rw [h0, h1, h2]
    simp only [C_0, C_1, zero_mul, add_zero, one_mul]
    rw [← pow_mul]; ring

/-- F_L = 2^(m+3) * odd and F_(L-1) = 1 + 2^(m+2) + 2^(m+3) t for L = 3 * 2^(m+1). -/
lemma fib_L (m : ℕ) : ∃ K u t, 3 * 2 ^ (m + 1) = K + 1 ∧ Nat.fib (K + 1) = 2 ^ (m + 3) * (2 * u + 1) ∧
    Nat.fib K = 1 + 2 ^ (m + 2) + 2 ^ (m + 3) * t := by
  induction m with
  | zero => exact ⟨5, 0, 0, by norm_num, by decide, by decide⟩
  | succ m ih =>
    obtain ⟨K, u, t, hK, hu, ht⟩ := ih
    have hfib1 : Nat.fib (K + 2) = Nat.fib K + Nat.fib (K + 1) := Nat.fib_add_two
    refine ⟨2 * K + 1, ?_, t + 2 ^ m * (1 + 2 * t) ^ 2 + 2 ^ (m + 2) * (2 * u + 1) ^ 2, ?_, ?_, ?_⟩
    · exact 2 * u * (2 ^ (m + 2) * (1 + t + u)) + u + 2 ^ (m + 2) * (1 + t + u)
    · rw [pow_succ 2 (m + 1)]; omega
    · rw [show 2 * K + 1 + 1 = 2 * (K + 1) by ring, Nat.fib_two_mul, show K + 1 + 1 = K + 2 by ring,
        hfib1, hu, ht]
      have : 2 * (1 + 2 ^ (m + 2) + 2 ^ (m + 3) * t + 2 ^ (m + 3) * (2 * u + 1)) -
          2 ^ (m + 3) * (2 * u + 1) = 2 * (1 + 2 ^ (m + 2) + 2 ^ (m + 3) * t) + 2 ^ (m + 3) * (2 * u + 1) := by
        omega
      rw [this]; ring
    · rw [Nat.fib_two_mul_add_one, hu, ht]; ring

/-- Bit n = m+2 of F_k flips after L = 3 * 2^(m+1) steps exactly when F_k is odd. -/
lemma flipF (m k : ℕ) :
    ((Nat.fib (k + 3 * 2 ^ (m + 1)) / 2 ^ (m + 2) : ℕ) : ZMod 2) =
      ((Nat.fib k / 2 ^ (m + 2) : ℕ) : ZMod 2) + ((Nat.fib k : ℕ) : ZMod 2) := by
  obtain ⟨K, u, t, hK, hu, ht⟩ := fib_L m
  have e : Nat.fib (k + 3 * 2 ^ (m + 1)) =
      Nat.fib k + 2 ^ (m + 2) * (Nat.fib k * (1 + 2 * t) + Nat.fib (k + 1) * (2 * (2 * u + 1))) := by
    rw [hK, ← add_assoc, Nat.fib_add, hu, ht]; ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.cast_add]
  congr 1
  push_cast
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2]; ring

end A037097

open A037097

/-- OEIS A036284(n) as a GF(2)[X] polynomial: sum_{k < 3*2^n} bit_n(F_k) X^k. -/
noncomputable def A036284poly (n : ℕ) : (ZMod 2)[X] := colPoly Nat.fib n (3 * 2 ^ n)

/-- Both conjectures of A036284: for n ≥ 1, (X^3+1)^(2^(n-1) - 1) * (X + 1) divides a(n). -/
theorem A036284_dvd (n : ℕ) (hn : 1 ≤ n) :
    (X ^ 3 + 1) ^ (2 ^ (n - 1) - 1) * (X + 1) ∣ A036284poly n := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | h2
  · subst h1
    refine ⟨X ^ 3, ?_⟩
    have h2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
    simp [A036284poly, colPoly, sum_range_succ, Nat.fib_add_two]
    linear_combination X ^ 5 * h2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsplit := colPoly_double Nat.fib (m + 2) (3 * 2 ^ (m + 1)) (fun k => (Nat.fib k : ZMod 2))
    (flipF m)
  rw [show 3 * 2 ^ (m + 1) = 3 * 2 ^ (m + 1) by rfl, fib_parity_sum, geom3,
    show (X : (ZMod 2)[X]) ^ (3 * 2 ^ (m + 1)) = (X ^ 3) ^ (2 ^ (m + 1)) by rw [pow_mul],
    one_add_pow_two_pow] at hsplit
  unfold A036284poly
  rw [show 3 * 2 ^ (m + 2) = 3 * 2 ^ (m + 1) + 3 * 2 ^ (m + 1) by rw [pow_succ 2 (m + 1)]; ring, hsplit,
    show m + 2 - 1 = m + 1 by omega]
  set A := colPoly Nat.fib (m + 2) (3 * 2 ^ (m + 1))
  have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  refine ⟨(X ^ 2 + X + 1) * A + X * (X ^ 3) ^ (2 ^ (m + 1)), ?_⟩
  rw [show ((X : (ZMod 2)[X]) ^ 3 + 1) ^ (2 ^ (m + 1)) = (X ^ 3 + 1) ^ (2 ^ (m + 1) - 1) * (X ^ 3 + 1) by
    rw [← pow_succ, Nat.sub_add_cancel hpos]]
  have hc : (X ^ 3 + 1 : (ZMod 2)[X]) = (X + 1) * (X ^ 2 + X + 1) := by
    have h2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
    linear_combination (-(X ^ 2 + X)) * h2
  rw [hc]
  ring

/-- The scan's older exponent A000225(n-1) = 2^(n-1) - 1 fails at n = 3: a(3) = x^2 + x^3. -/
theorem A037097_old_exponent_false : ¬ (X + 1) ^ (2 ^ (3 - 1) - 1) ∣ A037097poly 3 := by
  have h3 : A037097poly 3 = X ^ 2 * (X + 1) := by
    simp [A037097poly, colPoly, sum_range_succ]
    linear_combination X ^ 3 * (CharTwo.two_eq_zero : (2 : (ZMod 2)[X]) = 0)
  rw [h3]
  rintro ⟨r, hr⟩
  have hne : (X + 1 : (ZMod 2)[X]) ≠ 0 := X_add_C_ne_zero 1
  have h2 : (X : (ZMod 2)[X]) ^ 2 = (X + 1) ^ 2 * r := by
    apply mul_right_cancel₀ hne
    rw [hr]; norm_num; ring
  have := congrArg (eval 1) h2
  simp at this
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  rw [h11] at this
  simp at this
